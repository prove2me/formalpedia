-- Prove2me | Definitions.Def_OAIErdos3B055
-- name    : OAIErdos3B055
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T05:26:48.423112+00:00
-- url     : https://prove2.me/theorems/3868b4de-9d38-4cd2-95c1-90c51a291169
-- title:
--   OpenAI Erdős-3 split, definitions bundle 56 of 181
-- statement:
--   Definitions bundle 56 of 181 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B054`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 56 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.physicalResidueSpatialMaskMod`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueSpatialMaskMod_eval`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueSpatialMaskMod_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_originalDiagonalCorrection_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.originalDiagonalCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.originalDiagonalCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.originalDiagonalCorrection_pointwise_error`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitRealChart`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitRealChart_log`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitRealChart_polynomialCoordinates`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitRealChart_realEval`, `OAI.Erdos3.PolynomialPatch.ofWeightedChartShearOrbit`, `OAI.Erdos3.PolynomialPatch.ofWeightedChartShearOrbit_kernel`, `OAI.Erdos3.PolynomialPatch.ofWeightedChartShearOrbit_weight`, `OAI.Erdos3.ScalarSiteExpansion.Bounds`, `OAI.Erdos3.ScalarSiteExpansion.atCeilScale`, `OAI.Erdos3.ScalarSiteExpansion.casesOn`, `OAI.Erdos3.ScalarSiteExpansion.eval`, `OAI.Erdos3.ScalarSiteExpansion.integerEval`, `OAI.Erdos3.ScalarSiteExpansion.rescale`, `OAI.Erdos3.VectorPolynomial.exists_allocated_original_density_projection_law`, `OAI.Erdos3.baseAuxiliaryBoxCell`, `OAI.Erdos3.commonSitePeriod`, `OAI.Erdos3.refinedAuxiliaryBoxCell`, `OAI.Erdos3.refinedResidue_implies_base`, `OAI.Erdos3.scaledSiteCoordinates`, `OAI.Erdos3.scaledSiteFamilyFactor`, `OAI.Erdos3.siteFamilyCoefficient`, `OAI.Erdos3.siteFamilyEval`, `OAI.Erdos3.siteFamilyFactor`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B157
import Definitions.Def_OAIErdos3B173

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AuxiliaryBoxLaws
namespace OAI

section

namespace Erdos3

theorem refinedResidue_implies_base (M J : ℕ) (u w : ℤ)
    (hw : w ≡ u [ZMOD (M : ℤ)]) (x : ℤ) (hx : x ≡ w [ZMOD (M * J : ℕ)]) :
    x ≡ u [ZMOD (M : ℤ)] :=
  (Int.ModEq.of_dvd (by exact_mod_cast dvd_mul_right M J) hx).trans hw

noncomputable def baseAuxiliaryBoxCell {I : Type*} (a : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (M d : I → ℕ) (hd : ∀ i, 0 < d i)
    (u : I → ℤ) :
    IntegerResidueBox a (fun i => a i + N i) (fun i => (M i : ℤ)) u → AuxiliaryBoxLabels P M d u :=
  boxAuxiliaryCell a N P M d hd u (fun i => (M i : ℤ)) u (fun _ _ hx => hx)

noncomputable def refinedAuxiliaryBoxCell {I : Type*} (a : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (M d J : I → ℕ) (hd : ∀ i, 0 < d i)
    (u w : I → ℤ) (hw : ∀ i, w i ≡ u i [ZMOD (M i : ℤ)]) :
    IntegerResidueBox a (fun i => a i + N i) (fun i => (M i * J i : ℕ)) w → AuxiliaryBoxLabels P M d u :=
  boxAuxiliaryCell a N P M d hd u (fun i => (M i * J i : ℕ)) w
    (fun i => refinedResidue_implies_base (M i) (J i) (u i) (w i) (hw i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalDiagonalComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def originalDiagonalCorrection
    (F : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin 2 → ℤ) → ℂ)
    (a : Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim)
    (i : Fin W.outputDim) (c : Fin W.quadraticRoot.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ b : Fin 2 → Fin W.quadraticRoot.outputDim,
    (W.eval i x * star (tensorVector W.quadraticRoot.eval 2 b x)) * F a (b 0, b 1, c) x

theorem originalDiagonalCorrection_pointwise_error {N : ℕ} [NeZero N]
    (F : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin 2 → ℤ) → ℂ)
    (a : Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim)
    (i : Fin W.outputDim) (c : Fin W.quadraticRoot.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
        (W.eval i (fun k => ((x k).val : ℤ)) * W.quadraticRoot.eval c (fun _ => ((x 0).val : ℤ))) -
      W.originalDiagonalCorrection F a i c (fun k => ((x k).val : ℤ))‖ ≤
      ∑ b : Fin 2 → Fin W.quadraticRoot.outputDim,
        ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
            star (W.quadraticRoot.quadraticSquareTriple (b 0, b 1, c) (fun k => ((x k).val : ℤ))) -
          F a (b 0, b 1, c) (fun k => ((x k).val : ℤ))‖ := by
  let z : Fin 2 → ℤ := fun k => ((x k).val : ℤ)
  let R := W.quadraticRoot
  let D := R.cyclicDiagonalDerivative a x
  let T := tensorVector R.eval 2
  have hunit := tensorVector_unit R.eval R.unit_eval 2 z
  have hres := complex_unit_vector_resolution (fun b => T b z) hunit (W.eval i z)
  have hin : correlationInput (z 0) (z 1) = z := by funext k; fin_cases k <;> rfl
  have ht (b : Fin 2 → Fin R.outputDim) :
      star (R.quadraticSquareTriple (b 0, b 1, c) z) = T b z * R.eval c (fun _ => z 0) := by
    simp only [quadraticSquareTriple, star_star, hin, T, tensorVector, Fin.prod_univ_two]
  have heq : D * (W.eval i z * R.eval c (fun _ => z 0)) =
      ∑ b : Fin 2 → Fin R.outputDim,
        (W.eval i z * star (T b z)) * (D * star (R.quadraticSquareTriple (b 0, b 1, c) z)) := by
    calc
      _ = D * ((∑ b, (W.eval i z * star (T b z)) * T b z) * R.eval c (fun _ => z 0)) := by rw [← hres]
      _ = _ := by
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [ht]
        ring
  change ‖D * (W.eval i z * R.eval c (fun _ => z 0)) - W.originalDiagonalCorrection F a i c z‖ ≤ _
  rw [heq, originalDiagonalCorrection, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [← mul_sub, norm_mul]
  have hc : ‖W.eval i z * star (T b z)‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval i z)).trans
    dsimp [T, tensorVector]
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun k _ => R.norm_eval (b k) z)
  exact mul_le_of_le_one_left (norm_nonneg _) hc

theorem originalDiagonalCorrection_mean_error {N : ℕ} [NeZero N]
    (F : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
          star (W.quadraticRoot.quadraticSquareTriple b (fun k => ((x k).val : ℤ))) -
        F a b (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim)
    (i : Fin W.outputDim) (c : Fin W.quadraticRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
          (W.eval i (fun k => ((x k).val : ℤ)) * W.quadraticRoot.eval c (fun _ => ((x 0).val : ℤ))) -
        W.originalDiagonalCorrection F a i c (fun k => ((x k).val : ℤ))‖) ≤
      (W.quadraticRoot.outputDim : ℝ) ^ 2 * ε := by
  have hm := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => W.originalDiagonalCorrection_pointwise_error F a i c x)
  rw [Finset.expect_sum_comm] at hm
  apply hm.trans
  calc
    _ ≤ ∑ _b : Fin 2 → Fin W.quadraticRoot.outputDim, ε :=
      Finset.sum_le_sum (fun b _ => herr a (b 0, b 1, c))
    _ = _ := by simp

theorem exists_originalDiagonalCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p), 0 ≤ q →
      ∀ F : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
        (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
        (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (F a b))) →
      ∀ a i c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
        (W.originalDiagonalCorrection F a i c)) := by
  obtain ⟨A, _, hequiv⟩ := exists_explicit_quadratic_root_equivalence
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + X + 3 * (X + 1) + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B + 6 * (X + 1))
  refine ⟨C, hC, ?_⟩
  intro p q W hq F hF a i c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let t := (v + A) ^ A + v + 3 * (v + 1) + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hqr : q ≤ t := by
    have hh : 0 ≤ (v + A) ^ A := by positivity
    dsimp [v] at hh
    dsimp [t, v]
    linarith
  have hAr : (p + A) ^ A ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show p + A ≤ v + A by dsimp [v]; linarith) A).trans
    dsimp [t]
    linarith
  have hcost : (t + B) ^ B + 6 * (v + 1) ≤ (p + q + C) ^ C := by
    simpa [T, X, t, v, Polynomial.eval₂_pow] using hbudget v hv
  have hterm (b : Fin 2 → Fin W.quadraticRoot.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((t + B) ^ B)
        (fun x => (W.eval i x * star (tensorVector W.quadraticRoot.eval 2 b x)) * F a (b 0, b 1, c) x)) :=
    hmul ht ((Classical.choice ((hequiv W).expansion i b)).mono hAr)
      ((Classical.choice (hF a (b 0, b 1, c))).mono hqr)
  have hcard : (Fintype.card (Fin 2 → Fin W.quadraticRoot.outputDim) : ℝ) ≤ Real.exp (6 * (v + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget 2 p) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) W.quadraticRoot.output_bound _
      _ = Real.exp (2 * tensorPowerBudget 2 p) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (tensorPowerBudget 2 p) 2).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        norm_num [tensorPowerBudget]
        dsimp [v]
        linarith
  have hcoeff : (∑ _ : Fin 2 → Fin W.quadraticRoot.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp (6 * (v + 1)) := by
    simpa using hcard
  have E := (NativeIntegerExpansion.weightedSum (fun b => Classical.choice (hterm b))
    (fun _ => (1 : ℂ)) (by positivity : 0 ≤ 6 * (v + 1)) hcard hcoeff).mono hcost
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
    (fun x => W.originalDiagonalCorrection F a i c x)
  simpa only [originalDiagonalCorrection, one_mul] using E

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {A S : Type*} [Fintype A] [Fintype S]
variable {I : A → Type*} [∀ a, Fintype (I a)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

universe u v

structure ScalarSiteExpansion (S : Type u) where
  Term : Type v
  [termFinite : Fintype Term]
  period : Term → ℕ
  coefficient : Term → ℂ
  factor : (i : Term) → S → ZMod (period i) → ℝ → ℂ

attribute [local instance] ScalarSiteExpansion.termFinite

namespace ScalarSiteExpansion

variable {S : Type u} [Fintype S]

structure Bounds (e : ScalarSiteExpansion.{u,v} S) (T D C : ℝ) (L : ℝ≥0) (H : ℝ) : Prop where
  card_le : (Fintype.card e.Term : ℝ) ≤ T
  period_pos : ∀ i, 0 < e.period i
  period_le : ∀ i, (e.period i : ℝ) ≤ D
  coefficient_le : (∑ i, ‖e.coefficient i‖) ≤ C
  factor_bound : ∀ i s r x, ‖e.factor i s r x‖ ≤ 1
  lipschitz : ∀ i s r, LipschitzWith L (e.factor i s r)
  support : ∀ i s r x, H ≤ |x| → e.factor i s r x = 0

noncomputable def eval (e : ScalarSiteExpansion.{u,v} S) (y : S → ℤ) (x : S → ℝ) : ℂ :=
  ∑ i, e.coefficient i * ∏ s, e.factor i s (y s : ZMod (e.period i)) (x s)

noncomputable def integerEval (e : ScalarSiteExpansion.{u,v} S) (N : ℕ) (y : S → ℤ) : ℂ :=
  e.eval y (fun s => (y s : ℝ) / N)

end ScalarSiteExpansion
end Erdos3

end

section

namespace Erdos3.ScalarSiteExpansion

open scoped NNReal

universe u v

variable {S : Type u} {e : ScalarSiteExpansion.{u,v} S}

end Erdos3.ScalarSiteExpansion

end

section

namespace Erdos3.ScalarSiteExpansion
open scoped BigOperators NNReal Classical
universe u v
variable {S : Type u} [Fintype S]
attribute [local instance] ScalarSiteExpansion.termFinite

noncomputable def rescale (e : ScalarSiteExpansion.{u,v} S) (c : ℂ) (r : ℝ) : ScalarSiteExpansion.{u,v} S where
  Term := e.Term
  period := e.period
  coefficient i := c * e.coefficient i
  factor i s k x := e.factor i s k (r * x)

end Erdos3.ScalarSiteExpansion

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w

variable {A : Type u} {S : Type v} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion.{v,w} S)

noncomputable def siteFamilyCoefficient (k : ∀ a, (e a).Term) : ℂ :=
  ∏ a, (e a).coefficient (k a)

noncomputable def siteFamilyFactor (k : ∀ a, (e a).Term) (s : S)
    (r : ∀ a, ZMod ((e a).period (k a))) (x : A → ℝ) : ℂ :=
  ∏ a, (e a).factor (k a) s (r a) (x a)

noncomputable def siteFamilyEval (y : S → A → ℤ) (x : S → A → ℝ) : ℂ :=
  ∑ k, siteFamilyCoefficient e k * ∏ s,
    siteFamilyFactor e k s (fun a => (y s a : ZMod ((e a).period (k a)))) (x s)

variable {T D C H : A → ℝ} {L : ℝ≥0}
variable (h : ∀ a, (e a).Bounds (T a) (D a) (C a) L (H a))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {A S : Type*} [Fintype A] (e : A → ScalarSiteExpansion S)

noncomputable def commonSitePeriod (k : ∀ a, (e a).Term) : ℕ := ∏ a, (e a).period (k a)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

variable {A D S : Type*} [Fintype A] [Fintype D]

def scaledSiteCoordinates (selected : A → D) (scale : A → ℝ) (x : D → ℝ) : A → ℝ :=
  fun a => scale a * x (selected a)

variable (e : A → ScalarSiteExpansion S) (selected : A → D) (scale : A → ℝ)

noncomputable def scaledSiteFamilyFactor (k : ∀ a, (e a).Term) (s : S)
    (r : ∀ a, ZMod ((e a).period (k a))) (x : D → ℝ) : ℂ :=
  siteFamilyFactor e k s r (scaledSiteCoordinates selected scale x)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local instance] ScalarSiteExpansion.termFinite

variable {α : Type*} [Fintype α] [DecidableEq α]

end Erdos3

end

section

namespace Erdos3.ScalarSiteExpansion
open scoped BigOperators NNReal Classical
universe u v
variable {S : Type u} [Fintype S]

noncomputable def atCeilScale (e : ScalarSiteExpansion.{u,v} S) (K d : ℕ) (γ : ℝ) :
    ScalarSiteExpansion.{u,v} S :=
  e.rescale (((⌈γ * (K : ℝ)⌉₊ : ℝ) / K) ^ d : ℂ) ((⌈γ * (K : ℝ)⌉₊ : ℝ) / K)

end Erdos3.ScalarSiteExpansion

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {X A V : Type*} [Fintype X] [Fintype A]
variable (spatialPeriod : ℕ) (q : X → ℕ) (e : A → ScalarSiteExpansion V)
variable (k : ∀ a, (e a).Term) (idealPeriod : ℕ)

namespace BooleanCubeKernel

variable {K α : Type*} [Fintype K] [Fintype α]
variable (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (q : X → ℕ)
variable (b : ℝ) (r : ℝ≥0) {spatialPeriod M : ℕ}
variable (hM : ∀ x, q x * spatialPeriod ∣ M)
variable (t : X → SpatialSiteLabel α spatialPeriod b r) (s : Finset α)

noncomputable def physicalResidueSpatialMaskMod (u : X → ZMod M) : ℂ :=
  starVertexSiteFactor (fun i u => ∏ x,
    if ZMod.castHom (hM x) (ZMod (q x * spatialPeriod)) (u x) =
      ((physicalCubeVertexValue (physicalCubeRootDifferences root D base residue)
        (spatialStarVertex i) x + (q x : ℤ) * (((t x).1 i).val : ℤ) : ℤ) : ZMod (q x * spatialPeriod))
    then (1 : ℂ) else 0) s u

theorem physicalResidueSpatialMaskMod_eval (u : X → ℤ) :
    physicalResidueSpatialMaskMod root D base residue q b r hM t s (fun x => (u x : ZMod M)) =
      physicalResidueSpatialMask root D base residue q b r t s u := by
  simp only [physicalResidueSpatialMaskMod, physicalResidueSpatialMask, starVertexSiteFactor,
    residueSiteIndicator, map_intCast, apply_ite, Complex.ofReal_one, Complex.ofReal_zero]

theorem physicalResidueSpatialMaskMod_norm (u : X → ZMod M) :
    ‖physicalResidueSpatialMaskMod root D base residue q b r hM t s u‖ ≤ 1 := by
  apply starVertexSiteFactor_bound
  intro i v
  rw [norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro x _
  split_ifs <;> simp

end BooleanCubeKernel
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchMarkedChartRestoration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

noncomputable def polynomialOrbitRealChart
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : F.realification.PolynomialOrbit w) : F.realification.PolynomialOrbit v :=
  polynomialOrbitOfLog (realChartSubstitute β g.log)
    (F.adapted_realChartSubstitute_weightedSupport w v β hβ g.adapted)

attribute [local irreducible] realChartSubstitute

@[simp] theorem polynomialOrbitRealChart_log
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : F.realification.PolynomialOrbit w) :
    (F.polynomialOrbitRealChart w v β hβ g).log = realChartSubstitute β g.log := by
  unfold polynomialOrbitRealChart
  exact polynomialOrbitOfLog_log _ _

attribute [local irreducible] polynomialOrbitRealChart

theorem polynomialOrbitRealChart_realEval
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : F.realification.PolynomialOrbit w) (x : τ → ℝ) :
    F.realification.polynomialOrbitRealEval v x (F.polynomialOrbitRealChart w v β hβ g) =
      F.realification.polynomialOrbitRealEval w (fun i => MvPolynomial.eval x (β i)) g := by
  apply NilpotentLieBCHGroup.ext
  simp only [polynomialOrbitRealEval_coord, polynomialOrbitRealChart_log]
  exact eval₂_realChartSubstitute β x g.log

end Erdos3.NilpotentLieFiltration

namespace Erdos3.PolynomialPatch

variable {σ τ ξ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)

noncomputable def ofWeightedChartShearOrbit (w : ξ → ℕ)
    (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit w) :
    PolynomialPatch τ s d :=
  A.ofShearOrbit ((polynomialShearFiltration A.weight s A.weight_le).polynomialOrbitRealChart
    w (fun _ : τ => 1) β hβ g)

@[simp] theorem ofWeightedChartShearOrbit_weight (w : ξ → ℕ)
    (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit w) :
    (A.ofWeightedChartShearOrbit w β hβ g).weight = A.weight := rfl

@[simp] theorem ofWeightedChartShearOrbit_kernel (w : ξ → ℕ)
    (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit w) :
    (A.ofWeightedChartShearOrbit w β hβ g).kernel = A.kernel := rfl

end Erdos3.PolynomialPatch

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

attribute [local irreducible] realChartSubstitute polynomialOrbitRealChart weightedAdaptedRealChartHom polynomialOrbitCoordinates

theorem polynomialOrbitRealChart_polynomialCoordinates
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : F.realification.PolynomialOrbit w) :
    F.realification.polynomialOrbitCoordinates v
      (F.polynomialOrbitRealChart w v β hβ g) =
    F.weightedAdaptedRealChartHom w v β hβ
      (F.realification.polynomialOrbitCoordinates w g) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  rw [F.realification.polynomialOrbitCoordinates_log, F.polynomialOrbitRealChart_log,
    F.weightedAdaptedRealChartHom_coord, F.realification.polynomialOrbitCoordinates_log]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.PolynomialPatch

open Module VectorPolynomial
open scoped TensorProduct

variable {σ τ ξ κ M : Type*} [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} (A : PolynomialPatch σ s d)
    (G : NilpotentLieFiltration M t)
    (φ : PolynomialShearLieAlgebra A.weight ℚ →ₗ⁅ℚ⁆ M)

local notation "F" => polynomialShearFiltration A.weight s A.weight_le

end Erdos3.PolynomialPatch

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedOriginalDensityProjectionLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

theorem exists_allocated_original_density_projection_law (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P W : ℝ} (_hP : 0 ≤ P) (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (D : ℕ)
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ),
    let density := allocatedCoefficientDensity B U basis hb o hR hσ S
    ∀ (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, 0} U
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) D density (f y))
    {Z : ℝ} (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ Real.exp P),
    let widths := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hwidths : ∀ z, 0 < widths z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∀ law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n)
      (Fin q) (allocatedPrincipalSides B U basis S)),
    let source := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride T widths hwidths hmass z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) base z) *
          (density (affineSampleCoefficientTorus U
            (fun j => translate (fun t => (base t : ℝ)) (p j))
            (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hm j))
            (fun k t => (z (k, t) : ℝ))) : ℂ))
    let projected := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride T widths hwidths hmass z).toReal : ℂ) *
        physicalCubePositiveTest U D p hm (f y) test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) base z)
    ‖law.complexMean source / (Z : ℂ) - law.complexMean projected / (Z : ℂ)‖ ≤ Real.exp (-P) := by
  obtain ⟨A₀, _, hprojection⟩ := exists_allocated_mixture_density_projection_law m q
  obtain ⟨b, _, hbnd⟩ := exists_positiveComparisonDataBudget_bound m q
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C b) ^ b + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ _ n B _ _ _ J _ U basis R σ S c x hb o hR hσ C V hC hV
    hσ1 Cinv hCinv hchart hsmall P W hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ
    hAP hCP hVP M hperiod X _ _ hX hdim p hp hm base stride hs hsP τ ξ hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank test htest T hT D f density hproject Z hZ hZi widths hwidths hmass
    law source projected
  let Q := positiveComparisonDataBudget m q P
  obtain ⟨hQ, hPQ, haccQ, _, _⟩ := positiveComparisonDataBudget_bounds m q hP
  have hExp := Real.exp_le_exp.mpr hPQ
  have hcut : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    calc
      _ ≤ ((P + b) ^ b + A₀) ^ A₀ :=
        pow_le_pow_left₀ (add_nonneg hQ (Nat.cast_nonneg A₀))
          (add_le_add (hbnd P hP) le_rfl) A₀
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hbudget P hP
  obtain ⟨_, F, inst, frequency, coeff, hfreq, hcoeff, happ⟩ :=
    exists_allocated_positive_fourier_data B U basis hb o S C V hC hV q
      hR hσ hσ1 Cinv hCinv hchart hsmall hP hmSize hK hRP hσP hcount hI hn hJ hAP hL hCP hVP
  let _ := inst
  have hη : 0 < positiveProjectionAccuracy P := Real.exp_pos _
  have hηQ : (positiveProjectionAccuracy P)⁻¹ ≤ Real.exp Q := by
    simp only [positiveProjectionAccuracy, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr haccQ
  have he := hprojection B U basis S c x hQ (hK.trans hPQ) hW hroot
    (hWP.trans hExp) (hL.trans hExp) hperiod (hX.trans hPQ) (hdim.trans hPQ)
    frequency hfreq coeff hcoeff p hp hm base stride hs (fun t => (hsP t).trans hExp)
    hτ (hτP.trans hExp) hξ hξ1 (hξP.trans hExp) hη hηQ N
    (fun t => (Real.exp_le_exp.mpr hcut).trans (hsize t)) hrank
    ((Real.exp_le_exp.mpr hcut).trans hRank) test htest T hT density D f hproject hη.le happ hZ
    hwidths hmass law
  apply he.trans
  calc
    (2 * positiveProjectionAccuracy P + positiveProjectionAccuracy P) / Z =
        3 * positiveProjectionAccuracy P * Z⁻¹ := by ring
    _ ≤ 3 * positiveProjectionAccuracy P * Real.exp P :=
      mul_le_mul_of_nonneg_left hZi (by positivity)
    _ = 3 * Real.exp (-(P + 4)) := by
      rw [mul_assoc, positiveProjectionAccuracy, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp 4 * Real.exp (-(P + 4)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (-P) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI

end


