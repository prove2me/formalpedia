-- Prove2me | Definitions.Def_OAIE3v2B101
-- name    : OAIE3v2B101
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:30:17.870772+00:00
-- url     : https://prove2.me/theorems/08976e13-272b-4b21-a662-0893115450d9
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 103 of 311
-- statement:
--   Definitions bundle 103 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B087`, `OAIE3v2B088`, `OAIE3v2B090` of this split.
--
--   Modules: `Estimates/PolarizedCoefficientPermutation.lean`, `Estimates/RealProjectedCoefficientLift.lean`, `Estimates/RealifiedMultidegree.lean`, `Estimates/ReplicatedLieAction.lean`, `Estimates/WeightedOrbitNormalization.lean`, `Estimates/WeightedTranslationShearExponential.lean`, `FixedDensity/GeneratorCells.lean`, `Linear/CanonicalRankCompatibility.lean`, `Linear/DualLogarithmicDifferential.lean`, `Linear/RankHorizontalSymbol.lean`, `Linear/RealDualRationalBounds.lean`, `Linear/RealRankHorizontalSymbol.lean`, `Linear/WeightedTranslationBasisHeight.lean`, `Nilpotent/NiltestBasepointNormalization.lean`, `Nilpotent/PolynomialShearBCH.lean`, `Nilpotent/PolynomialShearBCHOver.lean`, `Nilpotent/RealifiedBCHFiniteAtlas.lean`, `Polynomial/DilationPairPolynomial.lean`, `Polynomial/PolynomialPatchShearOrbitConverse.lean`, `Polynomial/PolynomialShearAffineExponential.lean`, `Polynomial/PolynomialShearFactorialIntegrality.lean`, `Polynomial/PolynomialShearRealGroup.lean`, `Polynomial/PolynomialShearWeightedOrbitCoordinates.lean`, `Polynomial/PolynomialSymbolicShearWeightedDegree.lean`, `Polynomial/RealAdaptedPolynomialGroup.lean`, `Polynomial/RealCoordinatePolynomialSymbol.lean`, `Polynomial/ScaledPolynomialDualBounds.lean`, `Polynomial/WeightedPolynomialEndomorphisms.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B087
import Definitions.Def_OAIE3v2B088
import Definitions.Def_OAIE3v2B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedMultidegree
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realLayer_antitone : Antitone F.realLayer :=
  fun _ _ h => Submodule.baseChange_mono ℝ (F.antitone h)

theorem realLayer_zero : F.realLayer 0 = ⊤ := by
  have h : F.layerIdeal 0 = ⊤ := by
    ext x
    change x ∈ F.layer 0 ↔ x ∈ (⊤ : Submodule ℚ L)
    rw [F.zero_eq_top]
  simp only [realLayer, h, LieSubmodule.baseChange_top]

theorem realLayer_terminal (a : σ → ℕ) (ha : ¬a ≤ bound) : F.realLayer a = ⊥ := by
  have h : F.layerIdeal a = ⊥ := by
    ext x
    change x ∈ F.layer a ↔ x ∈ (⊥ : Submodule ℚ L)
    rw [F.terminal a ha]
  simp only [realLayer, h, LieSubmodule.baseChange_bot]

theorem realLayer_lie_mem {a b : σ → ℕ} {x y : ℝ ⊗[ℚ] L}
    (hx : x ∈ F.realLayer a) (hy : y ∈ F.realLayer b) : ⁅x, y⁆ ∈ F.realLayer (a + b) := by
  have h : ⁅F.layerIdeal a, F.layerIdeal b⁆ ≤ F.layerIdeal (a + b) := by
    rw [LieSubmodule.lie_le_iff]
    exact fun x hx y hy => F.lie_mem hx hy
  have hreal : ⁅F.realLayer a, F.realLayer b⁆ ≤ F.realLayer (a + b) := by
    rw [realLayer, realLayer, ← LieSubmodule.lie_baseChange]
    exact Submodule.baseChange_mono ℝ h
  exact hreal (LieSubmodule.lie_mem_lie hx hy)

theorem realLayer_degree_eq (n : ℕ) :
    (F.ordinary.realLayer n).toSubmodule =
      ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), (F.realLayer a).toSubmodule := by
  change (F.ordinary.layer n).baseChange ℝ =
    ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), (F.layer a).baseChange ℝ
  rw [F.degree_eq]
  simp only [real_baseChange_iSup]

noncomputable def realification : MultidegreeLieFiltration σ (ℝ ⊗[ℚ] L) s bound where
  ordinary := F.ordinary.realification
  layer a := (F.realLayer a).toSubmodule.restrictScalars ℚ
  antitone := F.realLayer_antitone
  zero_eq_top := by rw [F.realLayer_zero]; rfl
  lie_mem := F.realLayer_lie_mem
  terminal a ha := by rw [F.realLayer_terminal a ha]; rfl
  degree_eq n := by
    change (F.ordinary.realLayer n).toSubmodule.restrictScalars ℚ = _
    rw [F.realLayer_degree_eq]
    simp only [real_restrictScalars_iSup]

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedOrbitNormalization
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem eval_zero_eq_coefficient (p : VectorPolynomial σ R V) :
    eval (fun _ => 0) p = coefficients p 0 := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v => simp [MvPolynomial.aeval_zero', MvPolynomial.constantCoeff_eq]
  | add p q hp hq => simp [hp, hq]

end Erdos3.VectorPolynomial

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

noncomputable def dilationPair (w : σ → ℕ) (q : ℚ) (p : VectorPolynomial σ ℚ L) :
    VectorPolynomial σ ℚ (L × L) := pair (weightedDilation w q p) p

@[simp] theorem coefficients_dilationPair (w : σ → ℕ) (q : ℚ)
    (p : VectorPolynomial σ ℚ L) (a : σ →₀ ℕ) :
    coefficients (dilationPair w q p) a =
      (q ^ Finsupp.weight w a • coefficients p a, coefficients p a) := by
  simp only [dilationPair, coefficients_pair, coefficients_weightedDilation]

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PolarizedCoefficientPermutation
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def polynomialOrbitOfLog (p : VectorPolynomial σ ℚ L) (hp : F.Adapted p) : F.PolynomialOrbit :=
  ⟨⟨p⟩, hp⟩

@[simp] theorem polynomialOrbitOfLog_eval (p : VectorPolynomial σ ℚ L) (hp : F.Adapted p)
    (x : σ → ℤ) :
    (F.polynomialOrbitEval x (F.polynomialOrbitOfLog p hp)).coord = eval (fun i => (x i : ℚ)) p := rfl

end Erdos3.MultidegreeLieFiltration

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

noncomputable def polynomialShearBasis [Fintype σ] (w : σ → ℕ) :
    Basis (PolynomialShearIndex w) R (PolynomialShearLieAlgebra w R) :=
  (Pi.basis (fun i => MvPolynomial.basisRestrictSupport R
    {a : σ →₀ ℕ | Finsupp.weight w a + 1 ≤ w i})).map (polynomialShearCoordinates w).symm

theorem polynomialShearBasis_repr [Fintype σ] (w : σ → ℕ)
    (D : PolynomialShearLieAlgebra w R) (a : PolynomialShearIndex w) :
    (polynomialShearBasis (R := R) w).repr D a = (D.val (X a.1)).coeff a.2.val := rfl

noncomputable def polynomialShearMonomial (w : σ → ℕ) (a : PolynomialShearIndex w) :
    PolynomialShearLieAlgebra w R := by
  classical
  refine ⟨MvPolynomial.mkDerivation R (Pi.single a.1 (monomial a.2.val 1)), ?_⟩
  intro i
  rw [MvPolynomial.mkDerivation_X]
  by_cases h : i = a.1
  · subst i
    rw [Pi.single_eq_same]
    exact (MvPolynomial.monomial_mem_restrictSupport R).mpr (Or.inl a.2.property)
  · rw [Pi.single_eq_of_ne h]
    exact Submodule.zero_mem _

theorem polynomialShearMonomial_X [DecidableEq σ] (w : σ → ℕ) (a : PolynomialShearIndex w) (i : σ) :
    (polynomialShearMonomial (R := R) w a).val (X i) =
      if i = a.1 then monomial a.2.val 1 else 0 := by
  classical
  rw [polynomialShearMonomial, MvPolynomial.mkDerivation_X]
  by_cases h : i = a.1
  · subst i
    simp only [Pi.single_eq_same, ite_true]
  · simp [h]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable {σ R : Type*} [CommRing R] {w : σ → ℕ}

noncomputable def polynomialShearAction (w : σ → ℕ) (n : ℕ) :
    PolynomialShearLieAlgebra w R →ₗ⁅R⁆ Module.End R (weightedSupportLE (R := R) w n) where
  toLinearMap :=
    { toFun := fun D => polynomialShearEnd D n
      map_add' := by
        intro D E
        apply LinearMap.ext
        intro P
        apply Subtype.ext
        rfl
      map_smul' := by
        intro c D
        apply LinearMap.ext
        intro P
        apply Subtype.ext
        rfl }
  map_lie' := by
    intro D E
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    rfl

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {σ R : Type*} [CommRing R] [Fintype σ]

theorem polynomialShearMonomial_repr (w : σ → ℕ) (a : PolynomialShearIndex w) :
    (polynomialShearBasis (R := R) w).repr (polynomialShearMonomial (R := R) w a) =
      Finsupp.single a 1 := by
  classical
  ext b
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  rw [polynomialShearBasis_repr, polynomialShearMonomial_X]
  by_cases hij : j = i
  · subst j
    by_cases hab : a = b
    · subst b
      simp
    · have hval : a.val ≠ b.val := fun h => hab (Subtype.ext h)
      simp [hab, hval]
  · simp [hij]

theorem polynomialShearBasis_eq_monomial (w : σ → ℕ) (a : PolynomialShearIndex w) :
    polynomialShearBasis (R := R) w a = polynomialShearMonomial w a := by
  apply (polynomialShearBasis (R := R) w).repr.injective
  rw [Basis.repr_self, polynomialShearMonomial_repr]

noncomputable def polynomialShearDeficit (w : σ → ℕ) (a : PolynomialShearIndex w) : ℕ :=
  w a.1 - Finsupp.weight w a.2.val

theorem polynomialShearBasis_mem_layer (w : σ → ℕ) (a : PolynomialShearIndex w) (r : ℕ)
    (hr : r ≤ polynomialShearDeficit w a) :
    polynomialShearBasis (R := R) w a ∈ polynomialShearLayer (R := R) w r := by
  classical
  rw [polynomialShearBasis_eq_monomial]
  intro i
  change (polynomialShearMonomial (R := R) w a).val (X i) ∈ weightedSupportDrop w (w i) r
  rw [polynomialShearMonomial_X]
  by_cases hi : i = a.1
  · subst i
    rw [if_pos rfl]
    apply (MvPolynomial.monomial_mem_restrictSupport R).mpr
    left
    change Finsupp.weight w a.2.val + r ≤ w a.1
    have h := a.2.property
    unfold polynomialShearDeficit at hr
    omega
  · rw [if_neg hi]
    exact Submodule.zero_mem _

theorem polynomialShearLayer_span (w : σ → ℕ) (r : ℕ) :
    polynomialShearLayer (R := R) w r =
      Submodule.span R (polynomialShearBasis (R := R) w '' {a | r ≤ polynomialShearDeficit w a}) := by
  classical
  apply le_antisymm
  · intro D hD
    apply (polynomialShearBasis (R := R) w).mem_span_image.mpr
    intro a ha
    have hc : (D.val (X a.1)).coeff a.2.val ≠ 0 := by
      simpa only [polynomialShearBasis_repr] using Finsupp.mem_support_iff.mp ha
    have h : Finsupp.weight w a.2.val + r ≤ w a.1 :=
      hD a.1 (MvPolynomial.mem_support_iff.mpr hc)
    change r ≤ w a.1 - Finsupp.weight w a.2.val
    omega
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact polynomialShearBasis_mem_layer w a r ha

@[instance_reducible]
noncomputable def polynomialShearIndexFintype (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    Fintype (PolynomialShearIndex w) := by
  classical
  have hfinite (i : σ) : {a : σ →₀ ℕ | Finsupp.weight w a + 1 ≤ w i}.Finite :=
    (Finsupp.finite_of_nat_weight_le w (fun j => (hw j).ne') (w i)).subset
      (fun a ha => (Nat.le_add_right (Finsupp.weight w a) 1).trans ha)
  letI (i : σ) : Fintype {a : σ →₀ ℕ // Finsupp.weight w a + 1 ≤ w i} := (hfinite i).fintype
  exact inferInstance

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

theorem polynomialShearExpOn_mono (D : PolynomialShearLieAlgebra w R)
    {m n : ℕ} (hmn : m ≤ n) (P : weightedSupportLE (R := R) w m) :
    (polynomialShearExpOn D n ⟨P.val, weightedSupportLE_mono hmn P.property⟩ :
      MvPolynomial σ R) = (polynomialShearExpOn D m P : MvPolynomial σ R) := by
  let inc : weightedSupportLE (R := R) w m →ₗ[R] weightedSupportLE (R := R) w n :=
    Submodule.inclusion (fun _ h => weightedSupportLE_mono hmn h)
  have hc : polynomialShearEnd D n ∘ₗ inc = inc ∘ₗ polynomialShearEnd D m := by
    ext Q
    rfl
  have h := Module.End.commute_exp_left_of_commute (polynomialShearEnd_isNilpotent D m)
    (polynomialShearEnd_isNilpotent D n) hc
  exact congrArg Subtype.val (LinearMap.congr_fun h P)

theorem polynomialShearExpOn_mul (D : PolynomialShearLieAlgebra w R) (m n : ℕ)
    (P : weightedSupportLE (R := R) w m) (Q : weightedSupportLE (R := R) w n) :
    (polynomialShearExpOn D (m + n) (weightedPolynomialMul w m n P Q) : MvPolynomial σ R) =
      (polynomialShearExpOn D m P : MvPolynomial σ R) *
        (polynomialShearExpOn D n Q : MvPolynomial σ R) := by
  have h := nilpotentExp_bilinear (weightedPolynomialMul (R := R) w m n)
    (polynomialShearEnd D m) (polynomialShearEnd D n) (polynomialShearEnd D (m + n))
    (polynomialShearEnd_isNilpotent D m) (polynomialShearEnd_isNilpotent D n)
    (polynomialShearEnd_isNilpotent D (m + n))
    (fun x y => Subtype.ext (by
      change D.val (x.val * y.val) = D.val x.val * y.val + x.val * D.val y.val
      rw [D.val.leibniz, smul_eq_mul, smul_eq_mul]
      ring)) P Q
  exact congrArg Subtype.val h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

theorem polynomialShearExp_eq_on (D : PolynomialShearLieAlgebra w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearExp D P = (polynomialShearExpOn D n ⟨P, hP⟩ : MvPolynomial σ R) :=
  (polynomialShearExpOn_mono D ((mem_weightedSupportLE_iff w n P).mp hP)
    ⟨P, (mem_weightedSupportLE_iff w _ P).mpr le_rfl⟩).symm

theorem polynomialShearExp_eq_sum (D : PolynomialShearLieAlgebra w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearExp D P = ∑ k ∈ Finset.range (n + 1),
      (k.factorial : ℚ)⁻¹ • (D.val.toLinearMap ^ k) P := by
  rw [polynomialShearExp_eq_on D hP]
  exact polynomialShearExpOn_sum D n ⟨P, hP⟩

theorem polynomialShearExp_add (D : PolynomialShearLieAlgebra w R)
    (P Q : MvPolynomial σ R) :
    polynomialShearExp D (P + Q) = polynomialShearExp D P + polynomialShearExp D Q := by
  let n := P.weightedTotalDegree w + Q.weightedTotalDegree w
  have hp : P ∈ weightedSupportLE w n :=
    (mem_weightedSupportLE_iff w n P).mpr (Nat.le_add_right _ _)
  have hq : Q ∈ weightedSupportLE w n :=
    (mem_weightedSupportLE_iff w n Q).mpr (Nat.le_add_left _ _)
  rw [polynomialShearExp_eq_on D ((weightedSupportLE w n).add_mem hp hq),
    polynomialShearExp_eq_on D hp, polynomialShearExp_eq_on D hq]
  exact congrArg Subtype.val ((polynomialShearExpOn D n).map_add ⟨P, hp⟩ ⟨Q, hq⟩)

theorem polynomialShearExp_mul (D : PolynomialShearLieAlgebra w R)
    (P Q : MvPolynomial σ R) :
    polynomialShearExp D (P * Q) = polynomialShearExp D P * polynomialShearExp D Q := by
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  have hq : Q ∈ weightedSupportLE w (Q.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ Q).mpr le_rfl
  rw [polynomialShearExp_eq_on D (weightedSupportLE_mul hp hq),
    polynomialShearExp_eq_on D hp, polynomialShearExp_eq_on D hq]
  exact polynomialShearExpOn_mul D _ _ ⟨P, hp⟩ ⟨Q, hq⟩

theorem polynomialShearExp_C (D : PolynomialShearLieAlgebra w R) (c : R) :
    polynomialShearExp D (C c) = C c := by
  rw [polynomialShearExp_eq_sum D (weightedSupportLE_C w 0 c)]
  simp

noncomputable def polynomialShearExpHom (D : PolynomialShearLieAlgebra w R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R where
  toFun := polynomialShearExp D
  map_one' := by simpa using polynomialShearExp_C D 1
  map_zero' := by simpa using polynomialShearExp_C D 0
  map_add' := polynomialShearExp_add D
  map_mul' := polynomialShearExp_mul D
  commutes' := polynomialShearExp_C D

theorem polynomialShearExp_sub_lower (D : PolynomialShearLieAlgebra w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearExp D P - P ∈ weightedSupportLT w n := by
  rw [polynomialShearExp_eq_sum D hP, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, Module.End.one_apply,
    one_smul, add_sub_cancel_right]
  apply (weightedSupportLT w n).sum_mem
  intro k hk
  have h := weightedDerivation_pow w D.val 1 D.property
    (show P ∈ weightedSupportDrop w n 0 by rwa [weightedSupportDrop_zero]) (k + 1)
  simp only [Nat.mul_one, Nat.zero_add] at h
  have hlow : (D.val.toLinearMap ^ (k + 1)) P ∈ weightedSupportLT w n := by
    rw [← weightedSupportDrop_one]
    exact weightedSupportDrop_antitone (Nat.le_add_left 1 k) h
  exact (weightedSupportLT (R := R) w n).restrictScalars ℚ |>.smul_mem _ hlow

noncomputable def polynomialShearExpAut (D : PolynomialShearLieAlgebra w R) :
    WeightedLoweringAut w R :=
  WeightedLoweringAut.ofHom w (polynomialShearExpHom D)
    (fun i => polynomialShearExp_sub_lower D (weightedSupportLE_X w i))

theorem polynomialShearExpAut_apply (D : PolynomialShearLieAlgebra w R)
    (P : MvPolynomial σ R) : (polynomialShearExpAut D).val P = polynomialShearExp D P := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolicShearWeightedDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R] [Algebra ℚ R]
variable {w₀ w₁ : σ → ℕ} {v₀ : τ → ℕ}

theorem polynomialShearExp_weightedSupportLE
    (D : PolynomialShearLieAlgebra w₀ R)
    (hD : ∀ i, D.val (X i) ∈ weightedSupportLE w₁ (w₁ i))
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w₁ n) :
    polynomialShearExp D P ∈ weightedSupportLE w₁ n := by
  have hP₀ : P ∈ weightedSupportLE w₀ (P.weightedTotalDegree w₀) :=
    (mem_weightedSupportLE_iff w₀ _ P).mpr le_rfl
  have hD₁ : ∀ i, D.val (X i) ∈ weightedSupportDrop w₁ (w₁ i) 0 := by
    simpa only [weightedSupportDrop_zero] using hD
  have hP₁ : P ∈ weightedSupportDrop w₁ n 0 := by
    simpa only [weightedSupportDrop_zero] using hP
  rw [polynomialShearExp_eq_sum D hP₀]
  apply ((weightedSupportLE (R := R) w₁ n).restrictScalars ℚ).sum_mem
  intro k hk
  apply ((weightedSupportLE (R := R) w₁ n).restrictScalars ℚ).smul_mem
  change (D.val.toLinearMap ^ k) P ∈ weightedSupportLE w₁ n
  simpa only [Nat.mul_zero, Nat.add_zero, weightedSupportDrop_zero] using
    weightedDerivation_pow w₁ D.val 0 hD₁ hP₁ k

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} {d : ℕ} (w : Fin d → ℕ)
variable [Fintype (PolynomialShearIndex w)]
variable (c : PolynomialShearIndex w → MvPolynomial σ ℝ)

noncomputable def polynomialSymbolicShearTerm (a : PolynomialShearIndex w) :
    MvPolynomial (σ ⊕ Fin d) ℝ :=
  rename Sum.inl (c a) * rename Sum.inr (monomial a.2.val 1)

omit [Fintype (PolynomialShearIndex w)] in
theorem polynomialSymbolicShearTerm_slot_degree (a : PolynomialShearIndex w) :
    polynomialSymbolicShearTerm w c a ∈
      weightedSupportLE (Sum.elim (fun _ : σ => 0) w) (Finsupp.weight w a.2.val) := by
  have hp : c a ∈ weightedSupportLE (fun _ : σ => 0) 0 := by
    intro α hα
    simp [Finsupp.weight_apply, Finsupp.sum]
  have hc := symbolic_rename_degree (fun _ : σ => 0)
    (Sum.elim (fun _ : σ => 0) w) Sum.inl (fun _ => rfl) hp
  have hm := symbolic_rename_degree w (Sum.elim (fun _ : σ => 0) w)
    Sum.inr (fun _ => rfl) (weightedSupportLE_monomial w a.2.val (1 : ℝ))
  exact (by simpa only [zero_add, polynomialSymbolicShearTerm] using weightedSupportLE_mul hc hm)

omit [Fintype (PolynomialShearIndex w)] in
theorem polynomialSymbolicShearTerm_total_degree
    (hc : ∀ a, c a ∈ weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a))
    (a : PolynomialShearIndex w) :
    polynomialSymbolicShearTerm w c a ∈
      weightedSupportLE (Sum.elim (fun _ : σ => 1) w) (w a.1) := by
  have hp := symbolic_rename_degree (fun _ : σ => 1)
    (Sum.elim (fun _ : σ => 1) w) Sum.inl (fun _ => rfl) (hc a)
  have hm := symbolic_rename_degree w (Sum.elim (fun _ : σ => 1) w)
    Sum.inr (fun _ => rfl) (weightedSupportLE_monomial w a.2.val (1 : ℝ))
  apply weightedSupportLE_mono _ (weightedSupportLE_mul hp hm)
  have ha := a.2.property
  unfold polynomialShearDeficit
  omega

noncomputable def polynomialSymbolicShearSlot (i : Fin d) : MvPolynomial (σ ⊕ Fin d) ℝ :=
  ∑ a : PolynomialShearIndex w, if a.1 = i then polynomialSymbolicShearTerm w c a else 0

theorem polynomialSymbolicShearSlot_lower (i : Fin d) :
    polynomialSymbolicShearSlot w c i ∈
      weightedSupportDrop (Sum.elim (fun _ : σ => 0) w) (w i) 1 := by
  classical
  apply Submodule.sum_mem
  intro a ha
  split_ifs with hi
  · intro α hα
    have h := polynomialSymbolicShearTerm_slot_degree w c a hα
    change Finsupp.weight (Sum.elim (fun _ : σ => 0) w) α ≤ Finsupp.weight w a.2.val at h
    have hb := a.2.property
    change Finsupp.weight (Sum.elim (fun _ : σ => 0) w) α + 1 ≤ w i
    have hiw := congrArg w hi
    omega
  · exact Submodule.zero_mem _

noncomputable def polynomialSymbolicShearDerivation :
    PolynomialShearLieAlgebra (Sum.elim (fun _ : σ => 0) w) ℝ := by
  refine ⟨MvPolynomial.mkDerivation ℝ (Sum.elim (fun _ => 0) (polynomialSymbolicShearSlot w c)), ?_⟩
  intro i
  rw [MvPolynomial.mkDerivation_X]
  cases i with
  | inl i => exact Submodule.zero_mem _
  | inr i => exact polynomialSymbolicShearSlot_lower w c i

theorem polynomialSymbolicShearDerivation_X_parameter (i : σ) :
    (polynomialSymbolicShearDerivation w c).val (X (Sum.inl i)) = 0 :=
  MvPolynomial.mkDerivation_X _ _ _

theorem polynomialSymbolicShearDerivation_X_slot (i : Fin d) :
    (polynomialSymbolicShearDerivation w c).val (X (Sum.inr i)) =
      polynomialSymbolicShearSlot w c i := MvPolynomial.mkDerivation_X _ _ _

theorem polynomialSymbolicShearDerivation_total_degree
    (hc : ∀ a, c a ∈ weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a))
    (i : σ ⊕ Fin d) :
    (polynomialSymbolicShearDerivation w c).val (X i) ∈
      weightedSupportLE (Sum.elim (fun _ : σ => 1) w) (Sum.elim (fun _ : σ => 1) w i) := by
  classical
  cases i with
  | inl i => rw [polynomialSymbolicShearDerivation_X_parameter]; exact Submodule.zero_mem _
  | inr i =>
    rw [polynomialSymbolicShearDerivation_X_slot]
    apply Submodule.sum_mem
    intro a ha
    split_ifs with hi
    · simpa only [hi, Sum.elim_inr] using polynomialSymbolicShearTerm_total_degree w c hc a
    · exact Submodule.zero_mem _

theorem polynomialSymbolicShearExp_total_degree
    (hc : ∀ a, c a ∈ weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a))
    {P : MvPolynomial (σ ⊕ Fin d) ℝ} {n : ℕ}
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n) :
    polynomialShearExp (polynomialSymbolicShearDerivation w c) P ∈
      weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n :=
  polynomialShearExp_weightedSupportLE _ (polynomialSymbolicShearDerivation_total_degree w c hc) hP

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearFactorialIntegrality
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

theorem polynomialShearLog_end (e : WeightedLoweringAut w R) (n : ℕ) :
    polynomialShearEnd (polynomialShearLog e) n = polynomialShearLogOn e n := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  exact polynomialShearLogValue_eq_on e P.property

theorem polynomialShearExp_degreeAction (D : PolynomialShearLieAlgebra w R) (n : ℕ) :
    ((polynomialShearExpAut D).degreeAction n).toLinearMap = polynomialShearExpOn D n := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  exact polynomialShearExp_eq_on D P.property

theorem polynomialShearExp_log (e : WeightedLoweringAut w R) :
    polynomialShearExpAut (polynomialShearLog e) = e := by
  apply Subtype.ext
  apply DFunLike.ext
  intro P
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  rw [polynomialShearExpAut_apply, polynomialShearExp_eq_on _ hp]
  unfold polynomialShearExpOn
  rw [polynomialShearLog_end, polynomialShearLogOn,
    exp_nilpotentLog (e.degreeAction_difference_nilpotent _)]
  simp [WeightedLoweringAut.degreeAction_apply_coe]

theorem polynomialShearLog_exp (D : PolynomialShearLieAlgebra w R) :
    polynomialShearLog (polynomialShearExpAut D) = D := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  change polynomialShearLogValue (polynomialShearExpAut D) (X i) = D.val (X i)
  rw [polynomialShearLogValue_eq_on _ (weightedSupportLE_X w i)]
  unfold polynomialShearLogOn
  rw [polynomialShearExp_degreeAction, polynomialShearExpOn,
    nilpotentLog_exp_sub_one (polynomialShearEnd_isNilpotent D (w i))]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialEndomorphisms
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem polynomialShearEnd_mem_drop (w : σ → ℕ) (s k : ℕ)
    {D : PolynomialShearLieAlgebra w R} (hD : D ∈ polynomialShearLayer (R := R) w k) :
    polynomialShearEnd D s ∈ weightedPolynomialEndDrop w s k := by
  intro n r P hP
  exact weightedDerivation_apply w D.val k hD hP

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolynomialShearBCH
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable {σ : Type*}

noncomputable def polynomialShearAssociativeAction (w : σ → ℕ) (s : ℕ) :
    PolynomialShearLieAlgebra w ℚ →ₗ⁅ℚ⁆ weightedPolynomialEndAlgebra (R := ℚ) w s where
  toLinearMap :=
    { toFun := fun D => ⟨polynomialShearEnd D s,
        weightedPolynomialEndDrop_antitone w s (Nat.zero_le 1)
          (polynomialShearEnd_mem_drop w s 1 D.property)⟩
      map_add' := by
        intro D E
        apply Subtype.ext
        exact (polynomialShearAction w s).map_add D E
      map_smul' := by
        intro c D
        apply Subtype.ext
        exact (polynomialShearAction w s).map_smul c D }
  map_lie' := by
    intro D E
    apply Subtype.ext
    exact (polynomialShearAction w s).map_lie D E

theorem polynomialShearAssociativeAction_positive (w : σ → ℕ) (s : ℕ)
    (D : PolynomialShearLieAlgebra w ℚ) :
    polynomialShearAssociativeAction w s D ∈ (weightedPolynomialEndFiltration w s).layer 1 :=
  polynomialShearEnd_mem_drop w s 1 D.property

theorem polynomialShearExpOn_lieBCH (w : σ → ℕ) (s : ℕ)
    (D E : PolynomialShearLieAlgebra w ℚ) :
    polynomialShearExpOn (lieBCH s D E) s = polynomialShearExpOn D s * polynomialShearExpOn E s := by
  let F := weightedPolynomialEndFiltration w s
  let φ := polynomialShearAssociativeAction w s
  have hp (A : PolynomialShearLieAlgebra w ℚ) : φ A ∈ F.layer 1 :=
    polynomialShearAssociativeAction_positive w s A
  have hnil (A : PolynomialShearLieAlgebra w ℚ) : IsNilpotent (φ A) :=
    F.isNilpotent_of_mem le_rfl (hp A)
  have he : IsNilpotent.exp (φ (lieBCH s D E)) = IsNilpotent.exp (φ D) * IsNilpotent.exp (φ E) := by
    rw [map_lieBCH, F.lieBCH_eq (hp D) (hp E)]
    exact exp_nilpotentBCH (F.layerAlgebra 1) F.positive_nilpotent (hp D) (hp E)
  have hv := congrArg (weightedPolynomialEndAlgebra (R := ℚ) w s).val he
  rw [map_mul, IsNilpotent.map_exp (hnil (lieBCH s D E)),
    IsNilpotent.map_exp (hnil D), IsNilpotent.map_exp (hnil E)] at hv
  exact hv

theorem polynomialShearExpAut_lieBCH (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)
    (D E : PolynomialShearLieAlgebra w ℚ) :
    polynomialShearExpAut (lieBCH s D E) = polynomialShearExpAut D * polynomialShearExpAut E := by
  apply WeightedLoweringAut.degreeActionHom_injective s hw
  apply LinearEquiv.toLinearMap_injective
  change ((polynomialShearExpAut (lieBCH s D E)).degreeAction s).toLinearMap =
    ((polynomialShearExpAut D).degreeAction s).toLinearMap *
      ((polynomialShearExpAut E).degreeAction s).toLinearMap
  rw [polynomialShearExp_degreeAction, polynomialShearExp_degreeAction,
    polynomialShearExp_degreeAction]
  exact polynomialShearExpOn_lieBCH w s D E

noncomputable def polynomialShearBCHEquiv (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearFiltration w s hw).Group ≃* WeightedLoweringAut w ℚ where
  toFun A := polynomialShearExpAut A.coord
  invFun e := ⟨polynomialShearLog e⟩
  left_inv A := NilpotentLieBCHGroup.ext (polynomialShearLog_exp A.coord)
  right_inv := polynomialShearExp_log
  map_mul' A B := polynomialShearExpAut_lieBCH w s hw A.coord B.coord

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolynomialShearBCHOver
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
attribute [local instance 100] LieRing.ofAssociativeRing

variable {σ R : Type*} [CommRing R] [Algebra ℚ R]

noncomputable def polynomialShearAssociativeActionOver (w : σ → ℕ) (s : ℕ) :
    PolynomialShearLieAlgebra w R →ₗ⁅R⁆ weightedPolynomialEndAlgebra (R := R) w s where
  toLinearMap :=
    { toFun := fun D => ⟨polynomialShearEnd D s,
        weightedPolynomialEndDrop_antitone w s (Nat.zero_le 1)
          (polynomialShearEnd_mem_drop w s 1 D.property)⟩
      map_add' := by
        intro D E
        apply Subtype.ext
        exact (polynomialShearAction w s).map_add D E
      map_smul' := by
        intro c D
        apply Subtype.ext
        exact (polynomialShearAction w s).map_smul c D }
  map_lie' := by
    intro D E
    apply Subtype.ext
    exact (polynomialShearAction w s).map_lie D E

noncomputable def polynomialShearAssociativeRatAction (w : σ → ℕ) (s : ℕ) :
    PolynomialShearLieAlgebra w R →ₗ⁅ℚ⁆ weightedPolynomialEndAlgebra (R := R) w s where
  toLinearMap := (polynomialShearAssociativeActionOver (R := R) w s).toLinearMap.restrictScalars ℚ
  map_lie' := by
    intro D E
    exact (polynomialShearAssociativeActionOver (R := R) w s).map_lie D E

theorem polynomialShearAssociativeActionOver_positive (w : σ → ℕ) (s : ℕ)
    (D : PolynomialShearLieAlgebra w R) :
    polynomialShearAssociativeRatAction (R := R) w s D ∈ (weightedPolynomialEndRatFiltration (R := R) w s).layer 1 :=
  polynomialShearEnd_mem_drop w s 1 D.property

theorem polynomialShearExpOn_lieBCH_over (w : σ → ℕ) (s : ℕ)
    (D E : PolynomialShearLieAlgebra w R) :
    polynomialShearExpOn (lieBCH s D E) s = polynomialShearExpOn D s * polynomialShearExpOn E s := by
  let F := weightedPolynomialEndRatFiltration (R := R) w s
  let φ := polynomialShearAssociativeRatAction (R := R) w s
  have hp (A : PolynomialShearLieAlgebra w R) : φ A ∈ F.layer 1 :=
    polynomialShearAssociativeActionOver_positive w s A
  have hnil (A : PolynomialShearLieAlgebra w R) : IsNilpotent (φ A) :=
    F.isNilpotent_of_mem le_rfl (hp A)
  have he : IsNilpotent.exp (φ (lieBCH s D E)) = IsNilpotent.exp (φ D) * IsNilpotent.exp (φ E) := by
    rw [map_lieBCH, F.lieBCH_eq (hp D) (hp E)]
    exact exp_nilpotentBCH (F.layerAlgebra 1) F.positive_nilpotent (hp D) (hp E)
  have hv := congrArg (weightedPolynomialEndAlgebra (R := R) w s).val he
  rw [map_mul, IsNilpotent.map_exp (hnil (lieBCH s D E)),
    IsNilpotent.map_exp (hnil D), IsNilpotent.map_exp (hnil E)] at hv
  exact hv

theorem polynomialShearExpAut_lieBCH_over (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)
    (D E : PolynomialShearLieAlgebra w R) :
    polynomialShearExpAut (lieBCH s D E) = polynomialShearExpAut D * polynomialShearExpAut E := by
  apply WeightedLoweringAut.degreeActionHom_injective s hw
  apply LinearEquiv.toLinearMap_injective
  change ((polynomialShearExpAut (lieBCH s D E)).degreeAction s).toLinearMap =
    ((polynomialShearExpAut D).degreeAction s).toLinearMap *
      ((polynomialShearExpAut E).degreeAction s).toLinearMap
  rw [polynomialShearExp_degreeAction, polynomialShearExp_degreeAction,
    polynomialShearExp_degreeAction]
  exact polynomialShearExpOn_lieBCH_over w s D E

noncomputable def polynomialShearBCHEquivOver (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearRatFiltration (R := R) w s hw).Group ≃* WeightedLoweringAut w R where
  toFun A := polynomialShearExpAut A.coord
  invFun e := ⟨polynomialShearLog e⟩
  left_inv A := NilpotentLieBCHGroup.ext (polynomialShearLog_exp A.coord)
  right_inv := polynomialShearExp_log
  map_mul' A B := polynomialShearExpAut_lieBCH_over w s hw A.coord B.coord

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearRealGroup
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S] {w : σ → ℕ}

theorem polynomialShearMap_monomial (f : R →+* S) (a : PolynomialShearIndex w) :
    polynomialShearMap f (polynomialShearMonomial w a) = polynomialShearMonomial w a := by
  classical
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialShearMap_X, polynomialShearMonomial_X, polynomialShearMonomial_X]
  split_ifs <;> simp

theorem polynomialShearMap_basis [Fintype σ] (f : R →+* S) (a : PolynomialShearIndex w) :
    polynomialShearMap f (polynomialShearBasis (R := R) w a) =
      polynomialShearBasis (R := S) w a := by
  rw [polynomialShearBasis_eq_monomial, polynomialShearBasis_eq_monomial,
    polynomialShearMap_monomial]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {σ : Type*} (w : σ → ℕ)

variable [Fintype σ]

theorem polynomialShearRealificationHom_basis (a : PolynomialShearIndex w) :
    polynomialShearRealificationHom w ((polynomialShearBasis (R := ℚ) w).baseChange ℝ a) =
      polynomialShearBasis (R := ℝ) w a := by
  change polynomialShearRealificationMap w ((polynomialShearBasis (R := ℚ) w).baseChange ℝ a) = _
  rw [Basis.baseChange_apply, polynomialShearRealificationMap_tmul, polynomialShearMap_basis, one_smul]

noncomputable def polynomialShearRealificationLinearEquiv :
    (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) ≃ₗ[ℝ] PolynomialShearLieAlgebra w ℝ :=
  ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr.trans
    (polynomialShearBasis (R := ℝ) w).repr.symm

theorem polynomialShearRealificationMap_eq :
    (polynomialShearRealificationHom w).toLinearMap =
      (polynomialShearRealificationLinearEquiv w).toLinearMap := by
  apply ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).ext
  intro a
  change polynomialShearRealificationHom w ((polynomialShearBasis (R := ℚ) w).baseChange ℝ a) = _
  rw [polynomialShearRealificationHom_basis]
  change polynomialShearBasis (R := ℝ) w a =
    (polynomialShearBasis (R := ℝ) w).repr.symm
      (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr
        (((polynomialShearBasis (R := ℚ) w).baseChange ℝ) a))
  apply (polynomialShearBasis (R := ℝ) w).repr.injective
  rw [LinearEquiv.apply_symm_apply, Basis.repr_self, Basis.repr_self]

noncomputable def polynomialShearRealificationEquiv :
    (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) ≃ₗ⁅ℝ⁆ PolynomialShearLieAlgebra w ℝ :=
  LieEquiv.ofBijective (polynomialShearRealificationHom w) (by
    change Function.Bijective (polynomialShearRealificationHom w).toLinearMap
    rw [polynomialShearRealificationMap_eq]
    exact (polynomialShearRealificationLinearEquiv w).bijective)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ] (w : σ → ℕ)

noncomputable def polynomialShearRealificationRatHom :
    (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) →ₗ⁅ℚ⁆ PolynomialShearLieAlgebra w ℝ where
  toLinearMap := (polynomialShearRealificationEquiv w).toLinearEquiv.toLinearMap.restrictScalars ℚ
  map_lie' := by
    intro D E
    exact (polynomialShearRealificationEquiv w).map_lie D E

noncomputable def polynomialShearRealGroupEquiv (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearFiltration w s hw).realification.Group ≃*
      (polynomialShearRatFiltration (R := ℝ) w s hw).Group where
  toFun g := ⟨polynomialShearRealificationEquiv w g.coord⟩
  invFun g := ⟨(polynomialShearRealificationEquiv w).symm g.coord⟩
  left_inv g := NilpotentLieBCHGroup.ext ((polynomialShearRealificationEquiv w).symm_apply_apply g.coord)
  right_inv g := NilpotentLieBCHGroup.ext ((polynomialShearRealificationEquiv w).apply_symm_apply g.coord)
  map_mul' g h :=
    NilpotentLieBCHGroup.ext (map_lieBCH (polynomialShearRealificationRatHom w) s g.coord h.coord)

noncomputable def polynomialShearRealAutEquiv (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearFiltration w s hw).realification.Group ≃* WeightedLoweringAut w ℝ :=
  (polynomialShearRealGroupEquiv w s hw).trans (polynomialShearBCHEquivOver w s hw)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationShearExponential
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

noncomputable def weightedShearGroupHom (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    (weightedFiltration w d hw).Group →* WeightedLoweringAut (shearWeight w d) ℚ :=
  (polynomialShearBCHEquiv _ d (shearWeight_le w d hw)).toMonoidHom.comp
    (NilpotentLieBCHGroup.map (weightedShearEmbedding w d))

@[simp] theorem weightedShearGroupHom_apply (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, w i ≤ d) (g : (weightedFiltration w d hw).Group) :
    weightedShearGroupHom w d hw g = polynomialShearExpAut (weightedShearEmbedding w d g.coord) := rfl

noncomputable def weightedShearRealGroupHom (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, w i ≤ d) :
    (weightedFiltration w d hw).realification.Group →*
      WeightedLoweringAut (shearWeight w d) ℝ :=
  (polynomialShearRealAutEquiv _ d (shearWeight_le w d hw)).toMonoidHom.comp
    (NilpotentLieBCHGroup.mapReal (realificationLieHom (weightedShearEmbedding w d)))

@[simp] theorem weightedShearRealGroupHom_apply (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, w i ≤ d) (g : (weightedFiltration w d hw).realification.Group) :
    weightedShearRealGroupHom w d hw g = polynomialShearExpAut
      (polynomialShearRealificationEquiv (shearWeight w d)
        (realificationLieHom (weightedShearEmbedding w d) g.coord)) := rfl

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

noncomputable def realShearEmbedding (w : σ → ℕ) (d : ℕ) :
    (ℝ ⊗[ℚ] weightedSubalgebra w d) →ₗ⁅ℝ⁆ PolynomialShearLieAlgebra (shearWeight w d) ℝ :=
  (polynomialShearRealificationEquiv (shearWeight w d)).toLieHom.comp
    (realificationLieHom (weightedShearEmbedding w d))

@[simp] theorem realShearEmbedding_tmul (w : σ → ℕ) (d : ℕ)
    (r : ℝ) (x : weightedSubalgebra w d) :
    realShearEmbedding w d (r ⊗ₜ[ℚ] x) =
      r • polynomialShearMap (algebraMap ℚ ℝ) (weightedShearEmbedding w d x) := rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationBasisHeight
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

noncomputable def topProjection (w : σ → ℕ) (d : ℕ) :
    PolynomialTranslationLie σ →ₗ[ℚ] PolynomialTranslationLie σ where
  toFun x := ⟨fun i => if w i = d then x.base i else 0, C (x.polynomial.coeff 0)⟩
  map_add' x y := by
    ext i
    · by_cases hi : w i = d <;> simp [hi]
    · simp
  map_smul' r x := by
    ext i
    · by_cases hi : w i = d <;> simp [hi]
    · simp

omit [Fintype σ] in
@[simp] theorem topProjection_base (w : σ → ℕ) (d : ℕ)
    (x : PolynomialTranslationLie σ) (i : σ) :
    (topProjection w d x).base i = if w i = d then x.base i else 0 := rfl

omit [Fintype σ] in
@[simp] theorem topProjection_polynomial (w : σ → ℕ) (d : ℕ)
    (x : PolynomialTranslationLie σ) :
    (topProjection w d x).polynomial = C (x.polynomial.coeff 0) := rfl

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ : Type*} [Fintype σ]

noncomputable def weightedCoordinatesEquiv (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) :
    weightedSubalgebra w d ≃ₗ[ℚ] (σ → ℚ) × weightedSupportLT (R := ℚ) w d where
  toFun x := (x.val.base, ⟨x.val.polynomial,
    by simpa only [← weightedSupportDrop_one] using x.property.2⟩)
  invFun x := ⟨⟨x.1, x.2.val⟩, ⟨fun i hi => by have := hw i; omega,
    by simpa only [weightedSupportDrop_one] using x.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def weightedBasis (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) :
    Basis (WeightedBasisIndex w d) ℚ (weightedSubalgebra w d) :=
  ((Pi.basisFun ℚ σ).prod
    (MvPolynomial.basisRestrictSupport ℚ {a : σ →₀ ℕ | Finsupp.weight w a < d})).map
    (weightedCoordinatesEquiv w d hw).symm

@[simp] theorem weightedBasis_repr_inl (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) (i : σ) :
    (weightedBasis w d hw).repr x (Sum.inl i) = x.val.base i := by
  change (Pi.basisFun ℚ σ).repr x.val.base i = _
  simp only [Pi.basisFun_repr]

@[simp] theorem weightedBasis_repr_inr (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    (weightedBasis w d hw).repr x (Sum.inr a) = x.val.polynomial.coeff a.val := by
  rfl

omit [Fintype σ] in
@[simp] theorem weightedBasisGrade_inr (w : σ → ℕ) (d : ℕ)
    (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    weightedBasisGrade w d (Sum.inr a) = d - Finsupp.weight w a.val := rfl

@[simp] theorem weightedBasis_projection_base (w : σ → ℕ) (d j : ℕ)
    (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d) (i : σ) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.base i =
      if w i = j then x.val.base i else 0 := by
  simpa only [weightedBasis_repr_inl, weightedBasisGrade_inl] using
    basisGradeProjection_repr (weightedBasis w d hw) (weightedBasisGrade w d) j x (Sum.inl i)

@[simp] theorem weightedBasis_projection_coeff (w : σ → ℕ) (d j : ℕ)
    (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d)
    (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.polynomial.coeff a.val =
      if d - Finsupp.weight w a.val = j then x.val.polynomial.coeff a.val else 0 := by
  simpa only [weightedBasis_repr_inr, weightedBasisGrade_inr] using
    basisGradeProjection_repr (weightedBasis w d hw) (weightedBasisGrade w d) j x (Sum.inr a)

end Erdos3.PolynomialTranslationLie

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

theorem bracket_coefficient_mem_rank_two (w : σ → ℕ)
    (p q : F.associatedDegree.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients ⁅p.val, q.val⁆ α ∈ F.layer (Finsupp.weight w α) 2 := by
  classical
  have hmono (β : σ →₀ ℕ) (x : L) (hx : x ∈ F.layer (Finsupp.weight w β) 2) :
      coefficients (monomial (R := ℚ) β x) α ∈ F.layer (Finsupp.weight w α) 2 := by
    by_cases hβα : β = α
    · subst β
      simpa using hx
    · simp [hβα]
  rw [← sum_monomial_coefficients p.val, ← sum_monomial_coefficients q.val]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients p.val).support (coefficients q.val).support
    (fun β => monomial (R := ℚ) β (coefficients p.val β))
    (fun γ => monomial (R := ℚ) γ (coefficients q.val γ))]
  simp only [map_sum, Finsupp.finsetSum_apply]
  apply Submodule.sum_mem
  intro β _
  apply Submodule.sum_mem
  intro γ _
  rw [lie_monomial]
  apply hmono
  rw [map_add]
  exact F.lie_mem (F.rankLayerCoefficient w β p).property (F.rankLayerCoefficient w γ q).property

theorem higherHorizontalCoefficient_lie (w : σ → ℕ) (α : σ →₀ ℕ)
    (p q : F.associatedDegree.adaptedLieSubalgebra w) :
    F.higherHorizontalCoefficient w α ⁅p, q⁆ = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact F.bracket_coefficient_mem_rank_two w p q α

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem higherHorizontalSymbolCoefficient_lie (w : σ → ℕ) (α : σ →₀ ℕ)
    (p q : F.associatedDegree.PolynomialSymbol w) :
    F.higherHorizontalSymbolCoefficient w α ⁅p, q⁆ = 0 := by
  obtain ⟨p, rfl⟩ := F.associatedDegree.polynomialSymbolMap_surjective w p
  obtain ⟨q, rfl⟩ := F.associatedDegree.polynomialSymbolMap_surjective w q
  rw [← LieHom.map_lie, F.higherHorizontalSymbolCoefficient_map]
  exact F.higherHorizontalCoefficient_lie w α p q

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealAdaptedPolynomialGroup
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem realAdaptedPolynomialMap_adapted (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realification.Adapted w (F.realAdaptedPolynomialMap w x) := by
  rw [F.realification.adapted_iff_coefficients]
  intro α
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    rw [F.realAdaptedPolynomialMap_coefficient_tmul]
    exact LieSubmodule.tmul_mem_baseChange_of_mem a (p.property α)
  | add x y hx hy =>
    rw [map_add, map_add, Finsupp.add_apply]
    exact Submodule.add_mem _ hx hy

noncomputable def realAdaptedPolynomialTensor :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ⁅ℚ⁆ F.realification.adaptedLieSubalgebra w where
  toLinearMap := (F.realAdaptedPolynomialMap w).toLinearMap.codRestrict
    (F.realification.adaptedSubmodule w) (fun x =>
      (F.realification.mem_adaptedSubmodule w _).mpr (F.realAdaptedPolynomialMap_adapted w x))
  map_lie' {x y} := by
    apply Subtype.ext
    exact (F.realAdaptedPolynomialMap w).map_lie x y

@[simp] theorem realAdaptedPolynomialTensor_coe (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    (F.realAdaptedPolynomialTensor w x : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) =
      F.realAdaptedPolynomialMap w x := rfl

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realAdaptedPolynomialTensor_coordinates
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}) :
    (b.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap w x) z.val.1) z.val.2 =
      ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr x z := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    rw [F.realAdaptedPolynomialMap_coefficient_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, F.adaptedMonomialBasis_repr]
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply, hx, hy]

include b ω hlayers in
theorem realAdaptedPolynomialTensor_surjective :
    Function.Surjective (F.realAdaptedPolynomialTensor w) := by
  intro p
  let c := supportedCoordinates (b.baseChange ℝ)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 ≤ ω z.2}
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  let x := ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr.symm c
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply coefficients.injective
  ext α
  apply (b.baseChange ℝ).repr.injective
  ext i
  by_cases h : Finsupp.weight w α ≤ ω i
  · have hc := F.realAdaptedPolynomialTensor_coordinates w b ω hlayers x ⟨(α, i), h⟩
    change (b.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap w x) α) i = _
    rw [hc]
    change (((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr
      (((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr.symm c)) ⟨(α, i), h⟩ = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · have hleft := (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp
      ((F.realification.adapted_iff_coefficients w _).mp
        (F.realAdaptedPolynomialMap_adapted w x) α) i h
    have hright := (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp (p.property α) i h
    exact hleft.trans hright.symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

abbrev RealAdaptedPolynomialGroup := (F.adaptedPolynomialFiltration w).realification.Group

noncomputable def realAdaptedPolynomialGroupHom :
    F.RealAdaptedPolynomialGroup w →* (F.realification.adaptedPolynomialFiltration w).Group :=
  NilpotentLieBCHGroup.map (F.realAdaptedPolynomialTensor w)

@[simp] theorem realAdaptedPolynomialGroupHom_log (g : F.RealAdaptedPolynomialGroup w) :
    ((F.realAdaptedPolynomialGroupHom w g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) =
      F.realAdaptedPolynomialMap w g.coord := rfl

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hlayers in
theorem realAdaptedPolynomialGroupHom_surjective : Function.Surjective (F.realAdaptedPolynomialGroupHom w) := by
  intro g
  obtain ⟨x, hx⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hlayers g.coord
  exact ⟨⟨x⟩, NilpotentLieBCHGroup.ext hx⟩

noncomputable def realAdaptedPolynomialGroupLift (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.RealAdaptedPolynomialGroup w :=
  (F.realAdaptedPolynomialGroupHom_surjective w b ω hlayers g).choose

@[simp] theorem realAdaptedPolynomialGroupHom_lift
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realAdaptedPolynomialGroupHom w (F.realAdaptedPolynomialGroupLift w b ω hlayers g) = g :=
  (F.realAdaptedPolynomialGroupHom_surjective w b ω hlayers g).choose_spec

end Erdos3.NilpotentLieFiltration

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

noncomputable def orbitEquivOfEq {G : NilpotentLieFiltration L s} (h : F = G)
    {σ : Type*} (w : σ → ℕ) : F.PolynomialOrbit w ≃* G.PolynomialOrbit w := by
  subst G
  exact MulEquiv.refl _

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealDualRationalBounds
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

noncomputable def realDualBasis (b : Basis ι ℝ L) : Basis (ι ⊕ ι) ℝ (DualLieAlgebra L) :=
  (b.prod b).map dualRealCoordinates.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScaledPolynomialDualBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def adaptedPolynomialConstantHom :
    (F.adaptedPolynomialFiltration w).Group →* F.Group :=
  NilpotentLieBCHGroup.map ((evalLie (0 : σ → ℚ)).comp (F.adaptedLieSubalgebra w).incl)

@[simp] theorem adaptedPolynomialConstantHom_coord
    (g : (F.adaptedPolynomialFiltration w).Group) :
    (F.adaptedPolynomialConstantHom w g).coord =
      coefficients (g.coord : VectorPolynomial σ ℚ L) 0 :=
  eval_zero_eq_coefficient _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def adaptedConstantLieHom : L →ₗ⁅ℚ⁆ F.adaptedLieSubalgebra w where
  toFun := F.adaptedConstant w
  map_add' a b := by
    apply Subtype.ext
    exact TensorProduct.tmul_add _ _ _
  map_smul' a b := by
    apply Subtype.ext
    exact TensorProduct.tmul_smul a _ _
  map_lie' {a b} := by
    apply Subtype.ext
    change monomial 0 ⁅a, b⁆ = ⁅monomial 0 a, monomial 0 b⁆
    rw [lie_monomial, zero_add]

noncomputable def adaptedConstantGroupHom : F.Group →* (F.adaptedPolynomialFiltration w).Group :=
  NilpotentLieBCHGroup.map (F.adaptedConstantLieHom w)

@[simp] theorem adaptedConstantGroupHom_log (g : F.Group) :
    ((F.adaptedConstantGroupHom w g).coord : VectorPolynomial σ ℚ L) = monomial 0 g.coord := rfl

@[simp] theorem adaptedPolynomialConstantHom_constant (g : F.Group) :
    F.adaptedPolynomialConstantHom w (F.adaptedConstantGroupHom w g) = g := by
  apply NilpotentLieBCHGroup.ext
  rw [F.adaptedPolynomialConstantHom_coord, F.adaptedConstantGroupHom_log,
    coefficients_monomial, Finsupp.single_eq_same]

@[simp] theorem polynomialSymbolHom_constant (g : F.Group) :
    F.polynomialSymbolHom w (F.adaptedConstantGroupHom w g) = 1 := by
  apply NilpotentLieBCHGroup.ext
  exact F.polynomialSymbolMap_constant w g.coord

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

def PolynomialRationalGrid (l : ℕ) (g : (F.realification.adaptedPolynomialFiltration w).Group) : Prop :=
  (fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid l

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

def PolynomialSlowBound (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) : Prop :=
  ∀ α i, |(b.baseChange ℝ).repr
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤ M / monomialScale T α

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem linearPolynomial_adapted (a : σ → L) :
    linearPolynomial (R := ℚ) a ∈ F.adaptedLieSubalgebra (fun _ => 1) := by
  intro α
  by_cases h : ∃ i, Finsupp.single i 1 = α
  · obtain ⟨i, rfl⟩ := h
    rw [coefficients_linearPolynomial_single]
    simp only [Finsupp.weight_single, one_smul, F.one_eq_top, Submodule.mem_top]
  · rw [coefficients_linearPolynomial_of_ne a α (by simpa only [not_exists] using h)]
    exact Submodule.zero_mem _

noncomputable def linearPolynomialGroup (a : σ → L) :
    (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
  ⟨⟨linearPolynomial a, F.linearPolynomial_adapted a⟩⟩

@[simp] theorem linearPolynomialGroup_log (a : σ → L) :
    ((F.linearPolynomialGroup a).coord : VectorPolynomial σ ℚ L) = linearPolynomial a := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

noncomputable def affinePolynomialOrbit (b : L) (a : σ → L) :
    F.PolynomialOrbit (fun _ : σ => 1) :=
  polynomialOrbitOfLog (monomial 0 b + linearPolynomial a) (by
    apply (F.mem_adaptedSubmodule _ _).mp
    exact (F.adaptedSubmodule _).add_mem
      ((F.mem_adaptedSubmodule _ _).mpr (F.adapted_constant _ b))
      (F.linearPolynomial_adapted a))

@[simp] theorem affinePolynomialOrbit_log (b : L) (a : σ → L) :
    (F.affinePolynomialOrbit b a).log = monomial 0 b + linearPolynomial a := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealifiedBCHFiniteAtlas
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
  (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)

noncomputable def quotientCoordinateChart (z : NilpotentLieBCHGroup L s hnil) :
    OpenPartialHomeomorph (ι → ℝ) (NilpotentLieBCHGroup L s hnil ⧸ Γ) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let f := fun v : ι → ℝ => (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ)
  let U := {v : ι → ℝ | ∀ i, |v i| < bchInjectivityRadius s (Fintype.card ι) H l}
  have hi : Set.InjOn f U := (quotient_coordinate_injOn e c hstructure hc Γ l hl hgrid z).mono
    (fun _ hx i => (hx i).le)
  have hf : Continuous f := QuotientGroup.continuous_mk.comp
    (continuous_const.mul (basisHomeomorph e).symm.continuous)
  have ho : IsOpenMap f := QuotientGroup.isOpenMap_coe.comp
    ((Homeomorph.mulLeft z).isOpenMap.comp (basisHomeomorph e).symm.isOpenMap)
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (continuous_apply i).abs continuous_const)
  exact OpenPartialHomeomorph.ofContinuousOpen (hi.toPartialEquiv f U) hf.continuousOn ho hU

theorem quotientCoordinateChart_target (z : NilpotentLieBCHGroup L s hnil) :
    (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z).target =
      (fun v : ι → ℝ => (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ)) ''
        {v : ι → ℝ | ∀ i, |v i| < bchInjectivityRadius s (Fintype.card ι) H l} := rfl

theorem quotientCoordinateChart_center_mem (z : NilpotentLieBCHGroup L s hnil) :
    (QuotientGroup.mk z : _ ⧸ Γ) ∈ (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z).target := by
  have hzero : (basisHomeomorph (hnil := hnil) e).symm 0 = 1 := by
    apply (basisHomeomorph e).injective
    simp only [Homeomorph.apply_symm_apply, basisHomeomorph_apply, coord_one, map_zero]
  rw [quotientCoordinateChart_target]
  refine ⟨0, ?_, ?_⟩
  · intro i
    simpa only [Pi.zero_apply, abs_zero] using bchInjectivityRadius_pos s (Fintype.card ι) H l
  · simp only [hzero, mul_one]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set Manifold
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
  (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)

@[instance_reducible]
noncomputable def quotientChartedSpace : ChartedSpace (ι → ℝ) (NilpotentLieBCHGroup L s hnil ⧸ Γ) where
  atlas := Set.range (fun z => (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z).symm)
  chartAt := fun x => (quotientCoordinateChart e c hstructure hc Γ l hl hgrid x.out).symm
  mem_chart_source := fun x => by
    simpa only [OpenPartialHomeomorph.symm_source, QuotientGroup.out_eq'] using
      quotientCoordinateChart_center_mem e c hstructure hc Γ l hl hgrid x.out
  chart_mem_atlas := fun x => ⟨x.out, rfl⟩

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

local notation "G" => NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)

variable (e : Basis ι ℚ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (l : ℕ) (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)

@[instance_reducible]
noncomputable def realificationQuotientChartedSpace :
    ChartedSpace (ι → ℝ) (G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) :=
  NilpotentLieBCHGroup.quotientChartedSpace (e.baseChange ℝ) (lieStructureConstants e)
    (fun i j k => (realLieBasis_structure e i j k).symm) hc
    (Γ.map NilpotentLieBCHGroup.realificationHom) l hl
    (NilpotentLieBCHGroup.realification_subgroup_grid e Γ l houter)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

structure RationalFilteredNilmanifold (s d : ℕ) where
  filtration : NilpotentLieFiltration L s
  basis : Basis (Fin d) ℚ L
  layerBasis : ∀ i : Fin (s + 1),
    Basis (Fin (Module.finrank ℚ (filtration.layer (i.val + 1)))) ℚ (filtration.layer (i.val + 1))
  lattice : Subgroup filtration.Group
  grid : ℕ
  grid_pos : 0 < grid
  inner_grid : scaledIntegerGrid grid ⊆ bchSubgroupCoordinates basis lattice
  outer_grid : bchSubgroupCoordinates basis lattice ⊆ denominatorGrid grid

noncomputable def rationalLogHeight (q : ℚ) : ℝ :=
  Real.log (max (q.num.natAbs : ℝ) (q.den : ℝ))

namespace RationalFilteredNilmanifold

variable {L} {s d : ℕ} (D : RationalFilteredNilmanifold L s d)

abbrev RealGroup := D.filtration.realification.Group

noncomputable def realLattice : Subgroup D.RealGroup :=
  D.lattice.map NilpotentLieBCHGroup.realificationHom

abbrev Space : Type _ := D.RealGroup ⧸ D.realLattice

def GeometryComplexityLE (p : ℝ) : Prop :=
  (d : ℝ) ≤ p ∧ (D.grid : ℝ) ≤ Real.exp p ∧
  (∀ i j k, rationalLogHeight (lieStructureConstants D.basis i j k) ≤ p) ∧
  (∀ i j k, rationalLogHeight (D.basis.repr (D.layerBasis i j) k) ≤ p)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

@[instance_reducible]
noncomputable def metricSpace : MetricSpace D.Space :=
  realificationQuotientMetricSpace D.basis D.lattice D.grid D.grid_pos D.outer_grid

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

structure Niltest (w : σ → ℕ) where
  orbit : D.filtration.realification.PolynomialOrbit w
  observable : D.Space → ℂ
  normBound : ℝ≥0
  lipBound : ℝ≥0
  norm_le : ∀ x, ‖observable x‖ ≤ normBound
  lipschitz : letI := D.metricSpace; LipschitzWith lipBound observable

namespace Niltest

variable {D} {w : σ → ℕ}

noncomputable def const (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ) (c : ℂ) :
    D.Niltest w where
  orbit := 1
  observable := fun _ => c
  normBound := ‖c‖₊
  lipBound := 0
  norm_le _ := le_rfl
  lipschitz := by
    let := D.metricSpace
    exact LipschitzWith.const c

noncomputable def eval (T : D.Niltest w) (x : σ → ℤ) : ℂ :=
  T.observable (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x T.orbit))

@[simp] theorem eval_const (D : RationalFilteredNilmanifold L s d)
    (w : σ → ℕ) (c : ℂ) (x : σ → ℤ) : (const D w c).eval x = c := rfl

def ComplexityLE (T : D.Niltest w) (p : ℝ) : Prop :=
  D.GeometryComplexityLE p ∧ Real.log (2 + (T.normBound : ℝ) + (T.lipBound : ℝ)) ≤ p

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReplicatedLieAction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

structure MultidegreeStructure (D : RationalFilteredNilmanifold L s d) (bound : σ → ℕ) where
  filtration : MultidegreeLieFiltration σ L s bound
  ordinary : filtration.ordinary = D.filtration
  basis : ∀ a : ∀ i, Fin (bound i + 1),
    Basis (Fin (finrank ℚ (filtration.layer (fun i => (a i).val)))) ℚ
      (filtration.layer (fun i => (a i).val))

namespace MultidegreeStructure

variable {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

def ComplexityLE (p : ℝ) : Prop := D.GeometryComplexityLE p ∧
  ∀ a j k, rationalLogHeight (D.basis.repr (M.basis a j : L) k) ≤ p

noncomputable def orbitToOrdinary : M.filtration.realification.PolynomialOrbit →*
    D.filtration.realification.PolynomialOrbit (fun _ : σ => 1) := by
  have h : M.filtration.realification.ordinary = D.filtration.realification := by
    change M.filtration.ordinary.realification = D.filtration.realification
    rw [M.ordinary]
  exact (M.filtration.realification.ordinary.orbitEquivOfEq h (fun _ : σ => 1)).toMonoidHom.comp
    M.filtration.realification.toOrdinaryOrbit

end MultidegreeStructure

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeTwoVariableSplit (s d : ℕ) (p epsilon : ℝ)
    (f : (Fin 2 → ℤ) → ℂ) where
  count : ℕ
  count_pos : 0 < count
  count_bound : (count : ℝ) ≤ Real.exp p
  L : Bool → Type
  [lie : ∀ b, LieRing (L b)]
  [algebra : ∀ b, LieAlgebra ℚ (L b)]
  dim : Bool → ℕ
  [topology : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] L b)]
  [topologicalAdd : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] L b)]
  [continuousSMul : ∀ b, ContinuousSMul ℝ (ℝ ⊗[ℚ] L b)]
  [hausdorff : ∀ b, T2Space (ℝ ⊗[ℚ] L b)]
  model : ∀ b, RationalFilteredNilmanifold (L b) (∑ _ : Fin 2, s) (dim b)
  multi : ∀ b, (model b).MultidegreeStructure (totalDegreeSplitBound s b)
  complexity : ∀ b, (multi b).ComplexityLE p
  dimension_bound : ∀ b, dim b ≤ 2 ^ (2 * s) * d
  orbit : ∀ b, (multi b).filtration.realification.PolynomialOrbit
  test : ∀ b, Fin count → (model b).Niltest (fun _ : Fin 2 => 1)
  test_norm : ∀ b j, (test b j).normBound ≤ 1
  test_complexity : ∀ b j, (test b j).ComplexityLE p
  test_orbit : ∀ b j, (test b j).orbit = (multi b).orbitToOrdinary (orbit b)
  approximation : ∀ x,
    ‖f x - ∑ j, (test false j).eval x * (test true j).eval x‖ ≤ epsilon

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearWeightedOrbitCoordinates
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module VectorPolynomial
open scoped TensorProduct

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}
variable (s : ℕ) (hw : ∀ i, w i ≤ s)

theorem polynomialShearReal_adapted_iff_coordinate_support
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)) :
    (polynomialShearFiltration w s hw).realification.Adapted (fun _ : σ => 1) p ↔
      ∀ a : PolynomialShearIndex w,
        VectorPolynomial.coordinate
          (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p ∈
          weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a) := by
  rw [NilpotentLieFiltration.adapted_iff_coefficients]
  constructor
  · intro hp a α hα
    change α ∈ (VectorPolynomial.coordinate
      (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p).support at hα
    by_contra hdeg
    have hc := ((polynomialShearFiltration w s hw).real_mem_layer_iff_basis_coordinates
      (polynomialShearBasis (R := ℚ) w) (polynomialShearDeficit w)
      (fun j => polynomialShearLayer_span w j) _ _).mp (hp α) a hdeg
    apply (MvPolynomial.mem_support_iff.mp hα)
    rw [VectorPolynomial.coeff_coordinate]
    exact hc
  · intro hp α
    apply ((polynomialShearFiltration w s hw).real_mem_layer_iff_basis_coordinates
      (polynomialShearBasis (R := ℚ) w) (polynomialShearDeficit w)
      (fun j => polynomialShearLayer_span w j) _ _).mpr
    intro a ha
    change (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a)
      (VectorPolynomial.coefficients p α) = 0
    have hc : (VectorPolynomial.coordinate
        (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p).coeff α = 0 := by
      by_contra hne
      exact ha (hp a (MvPolynomial.mem_support_iff.mpr hne))
    exact (VectorPolynomial.coeff_coordinate _ p α).symm.trans hc

noncomputable def polynomialShearOrbitParameterCoordinates
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : σ => 1))
    (a : PolynomialShearIndex w) : MvPolynomial σ ℝ :=
  VectorPolynomial.coordinate
    (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom g.log

theorem polynomialShearOrbitParameterCoordinates_degree
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : σ => 1))
    (a : PolynomialShearIndex w) :
    polynomialShearOrbitParameterCoordinates s hw g a ∈
      weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a) :=
  (polynomialShearReal_adapted_iff_coordinate_support s hw g.log).mp g.adapted a

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbitConverse
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*} {s d : ℕ}

namespace PolynomialPatch

variable (A : PolynomialPatch σ s d)
  (f : MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ)

noncomputable def symbolicShearFullCenter (i : Fin d) : MvPolynomial (τ ⊕ Fin d) ℝ :=
  X (Sum.inr i) - f (rename Sum.inr (A.form.topResidualEquiv (X i)))

variable
  (hdegree : ∀ {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ},
    P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 1) A.weight) n →
    f P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 1) A.weight) n)

include hdegree in
theorem symbolicShearFullCenter_degree (i : Fin d) :
    A.symbolicShearFullCenter f i ∈
      weightedSupportLE (Sum.elim (fun _ : τ => 1) A.weight) (A.weight i) := by
  apply (weightedSupportLE _ _).sub_mem (weightedSupportLE_X _ (Sum.inr i))
  apply hdegree
  apply polynomialHom_preserves_weightedDegree A.weight _ (rename Sum.inr) _
    (A.form.topResidualEquiv_degree (weightedSupportLE_X A.weight i))
  intro j
  rw [rename_X]
  exact weightedSupportLE_X _ (Sum.inr j)

noncomputable def symbolicShearForm : PolynomialSlots τ d A.weight where
  center i := aeval (symbolicShearPrefixSubstitution i) (A.symbolicShearFullCenter f i)
  degree i := weightedSupportLE_aeval _ _ _
    (symbolicShearPrefixSubstitution_degree A.weight i)
    (A.symbolicShearFullCenter_degree f hdegree i)

noncomputable def symbolicShearPatch : PolynomialPatch τ s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := A.symbolicShearForm f hdegree
  kernel := A.kernel

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial

variable {τ : Type*} {d s : ℕ} {w : Fin d → ℕ}
variable [Fintype (PolynomialShearIndex w)]

noncomputable def polynomialShearOrbitSymbolicHom (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : τ => 1)) :
    MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ :=
  polynomialShearExpHom (polynomialSymbolicShearDerivation w
    (polynomialShearOrbitParameterCoordinates s hw g))

theorem polynomialShearOrbitSymbolicHom_degree (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : τ => 1))
    {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 1) w) n) :
    polynomialShearOrbitSymbolicHom hw g P ∈
      weightedSupportLE (Sum.elim (fun _ : τ => 1) w) n :=
  polynomialSymbolicShearExp_total_degree w _
    (polynomialShearOrbitParameterCoordinates_degree s hw g) hP

namespace PolynomialPatch
variable {σ : Type*} (A : PolynomialPatch σ s d)

noncomputable def ofShearOrbit
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) : PolynomialPatch τ s d := by
  letI := polynomialShearIndexFintype A.weight (fun i => A.weight_pos i)
  exact A.symbolicShearPatch (polynomialShearOrbitSymbolicHom A.weight_le g⁻¹)
    (polynomialShearOrbitSymbolicHom_degree A.weight_le g⁻¹)

@[simp] theorem ofShearOrbit_weight
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) : (A.ofShearOrbit g).weight = A.weight := rfl

@[simp] theorem ofShearOrbit_kernel
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) : (A.ofShearOrbit g).kernel = A.kernel := rfl

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealCoordinatePolynomialSymbol
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (v : σ → ℕ) (P : ι → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE v (ω i))

include hlayers hP

theorem real_ofCoordinates_adapted :
    F.realification.Adapted v (ofCoordinates (R := ℚ) (b.baseChange ℝ) P) := by
  classical
  apply (F.realification.adapted_iff_coefficients v _).mpr
  intro α
  change coefficients (ofCoordinates (R := ℚ) (b.baseChange ℝ) P) α ∈
    (F.realLayer (Finsupp.weight v α)).toSubmodule
  rw [coefficients_ofCoordinates, F.realLayer_eq_span_basis b _ _ (hlayers _)]
  apply Submodule.sum_mem
  intro i _
  by_cases hα : Finsupp.weight v α ≤ ω i
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hα, rfl⟩)
  · have hc : (P i).coeff α = 0 := by
      by_contra hne
      exact hα (hP i (MvPolynomial.mem_support_iff.mpr hne))
    rw [hc, zero_smul]
    exact Submodule.zero_mem _

noncomputable def realCoordinatePolynomialOrbit : F.realification.PolynomialOrbit v :=
  polynomialOrbitOfLog (ofCoordinates (R := ℚ) (b.baseChange ℝ) P)
    (F.real_ofCoordinates_adapted b ω hlayers v P hP)

@[simp] theorem realCoordinatePolynomialOrbit_log :
    (F.realCoordinatePolynomialOrbit b ω hlayers v P hP).log =
      ofCoordinates (R := ℚ) (b.baseChange ℝ) P := rfl

@[simp] theorem realCoordinatePolynomialOrbit_coordinate (i : ι) :
    coordinate ((b.baseChange ℝ).coord i).toAddMonoidHom
      (F.realCoordinatePolynomialOrbit b ω hlayers v P hP).log = P i :=
  coordinate_ofCoordinates (b.baseChange ℝ) P i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realExtendedSymbolMap :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ⁅ℚ⁆ F.RealPolynomialSymbol w :=
  LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) (F.polynomialSymbolMap w)

theorem realSymbolOfPolynomial_realAdaptedPolynomialMap
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realSymbolOfPolynomial b ω hlayers w (F.realAdaptedPolynomialMap w x) =
      F.realExtendedSymbolMap w x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    apply ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.injective
    ext z
    rw [F.realSymbolOfPolynomial_coordinate, F.realAdaptedPolynomialMap_coefficient_tmul]
    change (b.baseChange ℝ).repr (a ⊗ₜ[ℚ] coefficients (p : VectorPolynomial σ ℚ L) z.val.1) z.val.2 =
      ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
        (a ⊗ₜ[ℚ] F.polynomialSymbolMap w p) z
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul, F.polynomialSymbolBasis_repr_map]
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def realPolynomialSymbolMap :
    F.realification.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.RealPolynomialSymbol w where
  toLinearMap := (F.realSymbolOfPolynomial b ω hlayers w).comp
    (F.realification.adaptedLieSubalgebra w).incl.toLinearMap
  map_lie' {p q} := by
    change F.realSymbolOfPolynomial b ω hlayers w (↑⁅p, q⁆) =
      ⁅F.realSymbolOfPolynomial b ω hlayers w p, F.realSymbolOfPolynomial b ω hlayers w q⁆
    obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hlayers p
    obtain ⟨y, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hlayers q
    rw [← (F.realAdaptedPolynomialTensor w).map_lie x y]
    simp only [F.realAdaptedPolynomialTensor_coe, F.realSymbolOfPolynomial_realAdaptedPolynomialMap]
    exact (F.realExtendedSymbolMap w).map_lie x y

@[simp] theorem realPolynomialSymbolMap_apply (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolMap b ω hlayers w p = F.realSymbolOfPolynomial b ω hlayers w p := rfl

@[simp] theorem realPolynomialSymbolMap_representative (x : F.RealPolynomialSymbol w) :
    F.realPolynomialSymbolMap b ω hlayers w (F.realAdaptedSymbolRepresentative b ω hlayers w x) = x := by
  rw [F.realPolynomialSymbolMap_apply, F.realAdaptedSymbolRepresentative_coe,
    F.realSymbolOfPolynomial_representative]

noncomputable def realPolynomialSymbolHom :
    (F.realification.adaptedPolynomialFiltration w).Group →* F.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.realPolynomialSymbolMap b ω hlayers w)

@[simp] theorem realPolynomialSymbolHom_coord
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    (F.realPolynomialSymbolHom b ω hlayers w g).coord =
      F.realPolynomialSymbolMap b ω hlayers w g.coord := rfl

noncomputable def realPolynomialSymbolLift (g : F.RealPolynomialSymbolGroup w) :
    (F.realification.adaptedPolynomialFiltration w).Group :=
  ⟨F.realAdaptedSymbolRepresentative b ω hlayers w g.coord⟩

@[simp] theorem realPolynomialSymbolHom_lift (g : F.RealPolynomialSymbolGroup w) :
    F.realPolynomialSymbolHom b ω hlayers w (F.realPolynomialSymbolLift b ω hlayers w g) = g := by
  apply NilpotentLieBCHGroup.ext
  simp only [F.realPolynomialSymbolHom_coord, realPolynomialSymbolLift,
    F.realPolynomialSymbolMap_representative]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealProjectedCoefficientLift
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

include hφ in
theorem projectedComponent_mem_layer (k : Fin 4) (d : ℕ) (x : M) (hx : x ∈ F.layer d) :
    ((liePiEval k).comp φ) x ∈ G.associatedDegree.layer d := by
  change φ x k ∈ G.layer d 0
  rw [G.rank_zero_eq_one]
  exact hφ d x hx k

noncomputable def projectedComponentSymbolMap (w : σ → ℕ) (k : Fin 4) :
    F.PolynomialSymbol w →ₗ⁅ℚ⁆ G.associatedDegree.PolynomialSymbol w :=
  F.filteredPolynomialSymbolMap G.associatedDegree ((liePiEval k).comp φ)
    (G.projectedComponent_mem_layer F φ hφ k) w

noncomputable def projectedHorizontalSymbolCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.PolynomialSymbol w →ₗ[ℚ] (Fin 4 → G.HigherHorizontal (Finsupp.weight w α)) :=
  LinearMap.pi (fun k => (G.higherHorizontalSymbolCoefficient w α).comp
    (G.projectedComponentSymbolMap F φ hφ w k).toLinearMap)

theorem projectedHorizontalSymbolCoefficient_lie (w : σ → ℕ) (α : σ →₀ ℕ)
    (x y : F.PolynomialSymbol w) :
    G.projectedHorizontalSymbolCoefficient F φ hφ w α ⁅x, y⁆ = 0 := by
  funext k
  change G.higherHorizontalSymbolCoefficient w α
    ((G.projectedComponentSymbolMap F φ hφ w k) ⁅x, y⁆) = 0
  rw [LieHom.map_lie]
  exact G.higherHorizontalSymbolCoefficient_lie w α _ _

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

noncomputable def realProjectedHorizontalSymbolHom (ht : 1 ≤ t) (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.RealPolynomialSymbolGroup w →*
      Multiplicative (ℝ ⊗[ℚ] (Fin 4 → G.HigherHorizontal (Finsupp.weight w α))) where
  toFun X := Multiplicative.ofAdd
    ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ X.coord)
  map_one' := by
    change Multiplicative.ofAdd ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ 0) = 1
    rw [map_zero]
    rfl
  map_mul' X Y := by
    change Multiplicative.ofAdd ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
      (lieBCH t X.coord Y.coord)) = Multiplicative.ofAdd
        ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ X.coord +
          (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ Y.coord)
    exact congrArg Multiplicative.ofAdd (linearMap_baseChange_lieBCH_eq_add
      (G.projectedHorizontalSymbolCoefficient F φ hφ w α)
      (G.projectedHorizontalSymbolCoefficient_lie F φ hφ w α) ht X.coord Y.coord)

@[simp] theorem realProjectedHorizontalSymbolHom_apply (ht : 1 ≤ t) (w : σ → ℕ) (α : σ →₀ ℕ)
    (X : F.RealPolynomialSymbolGroup w) :
    Multiplicative.toAdd (G.realProjectedHorizontalSymbolHom F φ hφ ht w α X) =
      (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ X.coord := rfl

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r)

noncomputable def realFourHorizontalMap (d : ℕ) :
    (G.fourHorizontalLayer d).baseChange ℝ →ₗ[ℝ]
      ℝ ⊗[ℚ] (Fin 4 → G.HigherHorizontal d) :=
  ((G.fourHorizontalMap d).baseChange ℝ).comp
    (realificationSubmoduleEquiv (G.fourHorizontalLayer d)).symm.toLinearMap

@[simp] theorem realFourHorizontalMap_baseChange (d : ℕ)
    (v : ℝ ⊗[ℚ] G.fourHorizontalLayer d) :
    G.realFourHorizontalMap d (realificationSubmoduleEquiv (G.fourHorizontalLayer d) v) =
      (G.fourHorizontalMap d).baseChange ℝ v := by
  exact congrArg ((G.fourHorizontalMap d).baseChange ℝ)
    ((realificationSubmoduleEquiv (G.fourHorizontalLayer d)).symm_apply_apply v)

variable (F : NilpotentLieFiltration M t) (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

noncomputable def projectedLayerCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.adaptedLieSubalgebra w →ₗ[ℚ] G.fourHorizontalLayer (Finsupp.weight w α) :=
  (φ.toLinearMap.comp (F.adaptedCoefficientMap w α)).codRestrict
    (G.fourHorizontalLayer (Finsupp.weight w α))
    (fun p => (G.mem_fourHorizontalLayer _ _).mpr (hφ _ _ (p.property α)))

@[simp] theorem projectedLayerCoefficient_coe (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.adaptedLieSubalgebra w) :
    (G.projectedLayerCoefficient F φ hφ w α p : Fin 4 → L) = φ (coefficients p.val α) := rfl

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.GeneratorCells
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace FaceRegularityState

def refineBy (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) : FaceRegularityState Ω where
  partition :=
    FacePartition.join S.partition
      (FacePartition.generatedBy ({A} : Finset (Finset Ω)))

end FaceRegularityState

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualLogarithmicDifferential
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem base_lift_congr (f g : X → DualLieAlgebra L)
    (hb : ∀ x, dualBaseLinear (f x) = dualBaseLinear (g x)) (p : FreeLieAlgebra ℚ X) :
    dualBaseLinear (FreeLieAlgebra.lift ℚ f p) = dualBaseLinear (FreeLieAlgebra.lift ℚ g p) := by
  change dualBaseLie (FreeLieAlgebra.lift ℚ f p) = dualBaseLie (FreeLieAlgebra.lift ℚ g p)
  rw [map_freeLie_lift, map_freeLie_lift]
  exact congrArg (fun a : X → L => FreeLieAlgebra.lift ℚ a p) (funext hb)

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogDerivative_value_tangent (x y : L) :
    dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal y⟩ =
      dualTangentLinear (lieBCH s (dualConstantLie x + dualInfinitesimal y) (-dualConstantLie x)) := by
  change dualTangentLinear (lieBCH s (dualConstantLie x + dualInfinitesimal y)
    (-dualConstantLie (dualBaseLinear (dualConstantLie x + dualInfinitesimal y)))) = _
  rw [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealRankHorizontalSymbol
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def realHorizontalSymbolHom (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.RealPolynomialSymbolGroup w →*
      Multiplicative (ℝ ⊗[ℚ] F.HigherHorizontal (Finsupp.weight w α)) where
  toFun X := Multiplicative.ofAdd ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ X.coord)
  map_one' := by
    change Multiplicative.ofAdd ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ 0) = 1
    rw [map_zero]
    rfl
  map_mul' X Y := by
    change Multiplicative.ofAdd ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
      (lieBCH s X.coord Y.coord)) = Multiplicative.ofAdd
        ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ X.coord +
          (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ Y.coord)
    exact congrArg Multiplicative.ofAdd (linearMap_baseChange_lieBCH_eq_add
      (F.higherHorizontalSymbolCoefficient w α) (F.higherHorizontalSymbolCoefficient_lie w α)
      hs X.coord Y.coord)

end Erdos3.DegreeRankLieFiltration

end

end OAI
end


