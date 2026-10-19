-- Prove2me | Definitions.Def_OAIE3v2B252
-- name    : OAIE3v2B252
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:32:26.242833+00:00
-- url     : https://prove2.me/theorems/cb20f713-700a-47ec-b6f8-1d63975fd04a
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 257 of 311
-- statement:
--   Definitions bundle 257 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B237`, `OAIE3v2B238`, `OAIE3v2B240`, `OAIE3v2B241`, `OAIE3v2B242`, `OAIE3v2B243`, `OAIE3v2B244`, `OAIE3v2B245` of this split.
--
--   Modules: `Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean`, `Estimates/AllocatedExternalCandidateRefinementLabels.lean`, `Estimates/CoveredInducedCorrelationFamily.lean`, `Estimates/NativeResidualCrossInduction.lean`, `Estimates/ProductiveFrozenLocalMajorFamily.lean`, `Estimates/QuadraticBoundedFamily.lean`, `Estimates/RelativePatchPositivePowerInduction.lean`, `Estimates/UniformRelativePatchSource.lean`, `Geometry/ActualFixedSpatialRetainedModulusBudget.lean`, `Geometry/ActualFixedSpatialSlicedDataComparison.lean`, `Geometry/ActualFixedSpatialSlicedTargetReal.lean`, `Lattices/ActualFixedSpatialGoodPrimeDeletion.lean`, `Lattices/ActualFixedSpatialSlicedCRTIdentification.lean`, `Polynomial/PolynomialPatchTaggedBufferedScore.lean`, `Probability/AllocatedExternalCandidateAllKeptSliceLaw.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B237
import Definitions.Def_OAIE3v2B238
import Definitions.Def_OAIE3v2B240
import Definitions.Def_OAIE3v2B241
import Definitions.Def_OAIE3v2B242
import Definitions.Def_OAIE3v2B243
import Definitions.Def_OAIE3v2B244
import Definitions.Def_OAIE3v2B245

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily
namespace OAI

section

namespace Erdos3.QuadraticMarked

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def Model (t : ℕ) (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ) (p : ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp p ∧
    ∃ (d : ℕ) (D : RationalFilteredNilmanifold (Algebra t) 2 d),
      d ≤ 3 * t + 2 ∧ ∃ M : D.MultidegreeStructure (mixedCorrelationDegree 1),
        M.filtration = multidegree t ∧ M.ComplexityLE p ∧
        (∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (phase t m z.coord)) ∧
        (∀ a : Fin t → ℤ, (⟨(m : ℚ) • markedQuotientDirection
          filtration generators weights marked t (fun i => (a i : ℚ))⟩ : D.filtration.Group) ∈ D.lattice) ∧
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra t)
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra t) := IsModuleTopology.topologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 D.basis
         letI := D.metricSpace
         ∃ G : D.Space → ℂ, (∀ x, ‖G x‖ ≤ 2) ∧
           LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ G ∧
           ∀ g : D.RealGroup,
             (∀ i, |torusPhaseLinear (phase t m) g.coord i| ≤ 1 / 4) →
             G (QuotientGroup.mk g) = localCharacter m D η g)

theorem Model.mono {t : ℕ} {η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ}
    {p q : ℝ} (h : Model t η p) (hpq : p ≤ q) : Model t η q := by
  obtain ⟨m, hm, hmp, d, D, hd, M, hMF, hM, hint, hlat, hG⟩ := h
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hpq), d, D, hd, M, hMF,
    hM.mono M hpq, hint, hlat, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra t) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 D.basis
  let := D.metricSpace
  obtain ⟨G, hn, hl, he⟩ := hG
  exact ⟨G, hn, hl.weaken (Real.exp_le_exp.mpr hpq), he⟩

theorem exists_model_from_seed :
    ∃ C : ℕ, 2 ≤ C ∧ ∀
      [TopologicalSpace (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1)]
      [T2Space (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1)] {e : ℕ}
      (E : RationalFilteredNilmanifold (RationalTorus.BottomQuotient 1) 1 e)
      (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ) (V : E.Space → ℂ)
      {p : ℝ}, 1 ≤ p → ∀ t : ℕ, (t : ℝ) ≤ p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (lieQuotientMap (⊥ : LieIdeal ℚ Seed)
        (RationalTorus.basis 1 j)) i) ≤ p) →
      (∀ x, ‖V x‖ ≤ 1) →
      (letI := E.metricSpace; LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ V) →
      (∀ z : E.RealGroup, V (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z) →
      Model t η ((p + C) ^ C) := by
  obtain ⟨C, hC, hmodel⟩ := exists_induced_marked_model 1 1 (by decide)
  refine ⟨C, hC, ?_⟩
  intro _ _ _ _ e E η V p hp t ht hE hproj hVnorm hVLip hVeq
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  obtain ⟨m, hm, hmp, d, hdim, D, M, hMF, hM, hmap, hint, hlat, hG⟩ :=
    hmodel (t := t) filtration (RationalTorus.basis 1) weights filtration_layers (fun _ => le_rfl)
      generators weights marked weight_pos generator_mem (⊥ : LieIdeal ℚ Seed) second_marked_span
      E (fun _ : Unit => V) hp0 (by simpa only [Fintype.card_fin, Nat.cast_one] using hp)
      ht (structure_height hp0) (generator_height hp0) hE hproj
      (fun _ => hVnorm) (fun _ => hVLip)
  refine ⟨m, hm, hmp, d, D, ?_, M, hMF, hM, hint, hlat, ?_⟩
  · norm_num only [Fintype.card_fin, Nat.reduceAdd, pow_one, one_mul] at hdim
    omega
  · let := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra t)
    let : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra t) := IsModuleTopology.topologicalAddGroup ℝ _
    let := realification_moduleTopology_t2 D.basis
    let := D.metricSpace
    obtain ⟨G, hGnorm, hGLip, hGeq⟩ := hG
    refine ⟨G (), hGnorm (), hGLip (), ?_⟩
    intro g hg
    rw [hGeq () g hg, markedLocalCoefficientValue_apply, hVeq]
    rfl

theorem exists_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 1 ≤ p → ∀ t : ℕ, (t : ℝ) ≤ p →
      ∃ η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ,
        (∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0) ∧
        Model t η ((p + C) ^ C) := by
  obtain ⟨A, hA, hseed⟩ := RationalTorus.exists_bottom_quotient_character
  obtain ⟨B, _, hmodel⟩ := exists_model_from_seed
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p hp t ht
  classical
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (le_power_budget hp0 (a := A) (by omega)).trans
    change (p + 2) ^ A ≤ (p + A) ^ A
    exact pow_le_pow_left₀ (by linarith) (add_le_add le_rfl (by exact_mod_cast hA)) A
  have htotal : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp0
  have hBC : (q + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hq).trans htotal
  have hspan : (⊥ : LieIdeal ℚ Seed).toSubmodule =
      Submodule.span ℚ (RationalTorus.basis 1 '' (∅ : Set (Fin 1))) := by simp
  let qb := NilpotentLieFiltration.quotientFinBasis (RationalTorus.basis 1)
    (⊥ : LieIdeal ℚ Seed) ∅ hspan
  let := moduleTopology ℝ (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 qb
  obtain ⟨e, E, hE, hproj, η, V, hη, hVLip, hVnorm, hVeq⟩ := hseed 1 0 hp0 (by simpa using hp)
  have hm : Model t η ((q + B) ^ B) := hmodel E η V (hp.trans hpq) t (ht.trans hpq)
    (hE.mono E hpq) (fun i j => (hproj i j).trans hpq) (fun x => (hVnorm x).le) hVLip hVeq
  exact ⟨η, hη, hm.mono hBC⟩

end Erdos3.QuadraticMarked

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticBoundedFamily
namespace OAI

section

namespace Erdos3.QuadraticMarked

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem localCharacter_centeredElement {t d : ℕ}
    (D : RationalFilteredNilmanifold (Algebra t) 2 d)
    (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ)
    (hη : ∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0)
    (m : ℕ) (hm : 0 < m) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) (v : Fin t → ℝ) :
    localCharacter m D η (centeredElement t m a b n v) =
      CircleFourier.character ((n * (a + ∑ i, v i * b i) : ℝ) : CircleFourier.Circle) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hsum : a + ∑ i, ((m : ℝ) • v) i * ((m : ℝ)⁻¹ * b i) = a + ∑ i, v i * b i := by
    apply congrArg (a + ·)
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [localCharacter, centeredElement_retraction_coord D m hm]
  simp only [map_smul, smul_eq_mul]
  rw [shiftedLift_coordinate η hη, hsum]

end Erdos3.QuadraticMarked

end

section

namespace Erdos3.QuadraticMarked

open NilpotentLieBCHGroup
open scoped BigOperators

theorem localOrbit_observable {N t d : ℕ}
    (D : RationalFilteredNilmanifold (Algebra t) 2 d)
    (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ)
    (hη : ∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0)
    (m : ℕ) (hm : 0 < m)
    (hlat : ∀ a : Fin t → ℤ, (⟨(m : ℚ) • markedQuotientDirection
      filtration generators weights marked t (fun i => (a i : ℚ))⟩ : D.filtration.Group) ∈ D.lattice)
    (G : D.Space → ℂ)
    (hG : ∀ g : D.RealGroup, (∀ i, |torusPhaseLinear (phase t m) g.coord i| ≤ 1 / 4) →
      G (QuotientGroup.mk g) = localCharacter m D η g)
    (a : ℝ) (b u c : Fin t → ℝ) (h₀ h : ZMod N)
    (hsmall : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4) (n : ℤ) :
    G (QuotientGroup.mk ((multidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (localOrbit t m a b u c h₀))) =
        CircleFourier.character (((n : ℝ) * (a + ∑ i, affineCyclicTorusLocalLift u c h₀ h i * b i) : ℝ) :
          CircleFourier.Circle) := by
  rw [localOrbit_quotient D m hlat]
  apply (hG _ ?_).trans
    (localCharacter_centeredElement D η hη m hm a b n (affineCyclicTorusLocalLift u c h₀ h))
  intro i
  rw [centeredElement_phase D m hm]
  simpa only [Pi.neg_apply, abs_neg] using hsmall i

end Erdos3.QuadraticMarked

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualCrossInduction
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_native_residual_cross_row_detection_zero :
    ∃ C : ℕ, 2 ≤ C ∧ NativeResidualCrossRowDetection 0 C := by
  obtain ⟨A, _, hlinear⟩ := exists_characters_of_stepOne_rows
  obtain ⟨B, _, hdetect⟩ := exists_native_character_cross_row_detection 2 (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN f g R hf hg hR hRE hcorr
  let q := p + (p + A) ^ A
  have hpow : 0 ≤ (p + A) ^ A := by positivity
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hscore : (p + A) ^ A ≤ q := by dsimp [q]; linarith
  have hsum : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hresult : (q + B) ^ B ≤ (p + C) ^ C := by linarith
  let F (h n : ZMod N) := (f n * star (g (n + h))) *
    star (T.eval ![(h.val : ℤ), (n.val : ℤ)])
  have hF (h n : ZMod N) : ‖F h n‖ ≤ Real.exp p := by
    have hcross : ‖f n * star (g (n + h))‖ ≤ 1 := by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (hg (n + h))
    change ‖(f n * star (g (n + h))) * star (T.eval _)‖ ≤ _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) hcross).trans (T.eval_budget hT _)
  have hFcorr : Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      F h n * star (R h (fun _ => (n.val : ℤ)))‖) := by
    apply hcorr.trans_eq
    apply Finset.expect_congr rfl
    intro h _
    congr 1
    apply Finset.expect_congr rfl
    intro n _
    exact mul_right_comm _ _ _
  obtain ⟨χ, hχ⟩ := hlinear hp F R hF hR hRE hFcorr
  have hchars : Real.exp (-q) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      characterCrossRow f g χ h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hscore)).trans
    apply hχ.trans_eq
    apply Finset.expect_congr rfl
    intro h _
    congr 1
    unfold finiteFourierCoeff
    apply Finset.expect_congr rfl
    intro n _
    dsimp [F, characterCrossRow]
    ring
  exact (Real.exp_le_exp.mpr (neg_le_neg hresult)).trans
    (hdetect D T hq (hT.mono hpq) ((Real.exp_le_exp.mpr hresult).trans hN)
      f g χ hf hg hchars)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_native_residual_cross_row_detection (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeResidualCrossRowDetection s C := by
  induction s with
  | zero => exact exists_native_residual_cross_row_detection_zero
  | succ s ih =>
      obtain ⟨A, _, hdetect⟩ := ih
      exact exists_native_residual_cross_row_step hdetect

theorem RationalFilteredNilmanifold.exists_gowers_of_residual_cross_rows (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d)
      (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (f g : ZMod N → ℂ) (R : ZMod N → (Unit → ℤ) → ℂ),
      (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
      (∀ h (n : ZMod N), ‖R h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) p (R h))) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
        ((f n * star (g (n + h))) * star (R h (fun _ => (n.val : ℤ)))) *
          star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      Real.exp (-((p + C) ^ C)) ≤ gowersNorm (s + 1) g := by
  cases s with
  | zero => omega
  | succ s =>
      cases s with
      | zero => omega
      | succ s => exact exists_native_residual_cross_row_detection s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G T : Type*} {X : Type} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ} (hV : gridVolume ≠ 0)

local notation "Knative" => Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)

variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
variable (radius : ℝ≥0) (hradius0 : 0 < radius) (hradius3 : (3 : ℝ) ≤ radius)
variable (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
variable (chartCap : Fin m → ℝ) (hchartCap : ∀ j, 0 ≤ chartCap j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
  chartCap j * ‖v‖)
variable (hchartBudget : ∀ j, chartCap j * (((Fintype.card (I j) : ℝ) + 1) *
  (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ box i ≤ box i)
variable (htrimbase : base ∈ trimmedIntegerBox box (spatialTrimMargin τ box))
variable (hVpos : 0 < gridVolume)
variable {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
variable (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
variable (nativeCoeff : Findex → ℂ) (δnative : ℝ)
variable {Pambient Eprec Rrank M : ℝ} (hPambient : 0 ≤ Pambient) (hEprec : 0 ≤ Eprec)
variable (hX : (Fintype.card X : ℝ) ≤ Pambient)
variable (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ Pambient)
variable (hLip : ((Lip * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal coverCap) : ℝ≥0) : ℝ) ≤ Real.exp Pambient)
variable (hcoverF : ∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmodF : ∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmass : ∑ i, ‖nativeCoeff i‖ ≤ M)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (box i : ℝ))
  Rrank (U j) (nativePoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {D Pdecay δgrid : ℝ} (hD : 0 ≤ D)
variable (hPdecay : ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) + 2 : ℕ) : ℝ) ≤ Pdecay)
variable (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
variable (hgridmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
  forecastJointGridScale U basis R S.value box τ j ≤ δgrid)

local instance slicedAmbientRecoveredCoverNeZero_ra22e53_1 : NeZero W.cover := ⟨W.cover_pos.ne'⟩
noncomputable def allocatedSlicedPhysicalAmbientGridError : ℝ :=
  let lowerG := fun g => (cG g : ℝ) / S.value
  let widthG := fun g => (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value
  let frame := allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame
  let hwGne := fun g => ne_of_gt (fixedSpatialKernelProgression_width_pos S.positive
    (show (0 : ℤ) < stepG by exact_mod_cast hstepG) (hHG g))
  let slicedFrame := fixedSpatialKernelSliceFrame budget (S.value : ℝ) frame lowerG widthG
  let h0slice := fixedSpatialKernelBlock_slice_det_ne_zero e budget (S.value : ℝ) frame
    lowerG widthG false h0 hwGne
  let h1slice := fixedSpatialKernelBlock_slice_det_ne_zero e budget (S.value : ℝ) frame
    lowerG widthG true h1 hwGne
  let hδP : 0 < δ / 2 := div_pos hδ (by norm_num)
  let Cgrid := fixedSpatialOriginalForecastCap B
    (fixedSpatialKernelBlockEquiv e budget (S.value : ℝ) slicedFrame true h1slice) hδP
  let Lgrid := fixedSpatialOriginalForecastLip B
    (fixedSpatialKernelBlockEquiv e budget (S.value : ℝ) slicedFrame false h0slice)
    (fixedSpatialKernelBlockEquiv e budget (S.value : ℝ) slicedFrame true h1slice) hδP
  forecastJointGridError (Fintype.card Out)
    (Fintype.card (X ⊕ AllocatedActiveIntegerAxis U basis S.value))
    (Fintype.card (Σ j, I j)) cutoff D Lgrid Cgrid Knative δgrid

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateRefinementLabels
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace Refinement

variable {P} {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)

noncomputable def conclusion {outputCost outputMass outputScore : ℝ}
    (out : refinement.problem.Conclusion outputCost outputMass outputScore) :
    P.Conclusion outputCost outputMass outputScore where
  ambient := out.ambient
  marked := out.marked
  retained := out.retained
  subset := fun _ hz => refinement.subset (out.subset hz)
  mass := out.mass
  step := out.step
  step_pos := out.step_pos
  slice := out.slice
  dense := out.dense
  inside z := (out.inside z).trans
    (refinement.inside ⟨z.val, out.subset z.property⟩)
  score := out.score

end Refinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace Refinement
variable {P} {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)

noncomputable def restrictPaths (paths : Finset A.Path)
    (hpaths : paths ⊆ refinement.retained) {mass : ℝ} (hmass : mass ≤ A.law.mass paths) :
    P.Refinement newCost mass newScore where
  retained := paths
  subset := fun _ hz => refinement.subset (hpaths hz)
  mass := hmass
  cost_le := refinement.cost_le
  step z := refinement.step ⟨z.val, hpaths z.property⟩
  step_pos z := refinement.step_pos ⟨z.val, hpaths z.property⟩
  slice z := refinement.slice ⟨z.val, hpaths z.property⟩
  dense z := refinement.dense ⟨z.val, hpaths z.property⟩
  inside z := refinement.inside ⟨z.val, hpaths z.property⟩
  scoreLower z := refinement.scoreLower ⟨z.val, hpaths z.property⟩

end Refinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
namespace OAI

section

namespace Erdos3
open scoped TensorProduct BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

namespace UniversalLocalMajorSliceTest

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {N : I → ℕ} {degree : ℕ} {cost budget : ℝ}

theorem nonempty (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (degree : ℕ) (cost budget : ℝ) (hcost : 0 ≤ cost) (hbudget : 2 ≤ budget) :
    Nonempty (UniversalLocalMajorSliceTest N degree cost budget) :=
  ⟨default N hN degree cost budget hcost hbudget⟩

end UniversalLocalMajorSliceTest
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedTargetReal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

noncomputable def rawTarget (κ : ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ) : ℂ := by
  letI : NeZero slice.path.referenceModulus := ⟨slice.path.referenceModulus_pos.ne'⟩
  exact (κ : ℂ) * forecastLawDensityPhysicalTarget B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceInputLaw)
    (fun y t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (y k.1 k.2 : ℤ)) slice.path.referenceModulus t j)
    slice.path.referenceModulus (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW poly hm u

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ActualFixedSpatialSlicedCRTIdentification
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

local instance slicedReferenceModulusNeZero : NeZero slice.path.referenceModulus :=
  ⟨slice.path.referenceModulus_pos.ne'⟩

noncomputable def stepInputLaw : FiniteProbabilityWeights
    (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
      ZMod slice.path.referenceModulus) := by
  letI := slice.path.primeNeZero
  exact crtPolynomialInputLaw (fun p : slice.path.primes => p.val)
    (fun p : slice.path.primes => slice.path.exponent p.val)
    (fun p : slice.path.primes => padicValNat p.val slice.step)
    (primePower_crt_coprime (fun p : slice.path.primes => p.val)
      (fun p : slice.path.primes => slice.path.exponent p.val)
      (fun p => slice.path.prime p.val p.property) Subtype.val_injective)
    (fun p v => ((Sum.elim slice.kernelStart
      (fun a => slice.principalStart ⟨a.1.val,a.2⟩) v : ℤ) :
        ZMod (p.val ^ slice.path.exponent p.val)))

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedDataComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) physicalN τ δslice P Pbad Ppres)

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ δslice)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : slice.path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {t δ ε η : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
variable (hδ : 0 < δ) (hδone : δ ≤ 1)
variable (hdense : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), δ * S.value ≤
    ((integerProgressionSupport (slice.principalStart ⟨a.val,p⟩) (slice.step : ℤ)
      (slice.principalLength ⟨a.val,p⟩)).card : ℝ))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ slice.path.referenceModulus)
variable (hsizeG : ∀ g, q ≤ slice.kernelLength g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.kernelLength g) < 1)
variable (hsize : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), q ≤ slice.principalLength ⟨a.val,p⟩)
variable (hsmall : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
    scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.principalLength ⟨a.val,p⟩) < 1)
variable (hε : 0 ≤ ε) (hmesh : (slice.step : ℝ) / S.value ≤ ε)
variable (hη : 0 < η)
variable (htail : |t| * polynomialMassC2Budget
  (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
  slicedPrincipalC2Tolerance
    (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      B a.val × Fin (layerSamplerDegree I n a.val)))
    (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}) m 1
    (unitProfilePrincipalLowerBound B) (δ / 2) s.L η)

local notation "Active" => {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}
local notation "activeH" => (fun j : (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a))) =>
  slice.principalLength (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))
local notation "activeStart" => (fun j : (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a))) =>
  slice.principalStart (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))
local notation "Knative" => Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R)

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.actualComparisonReferenceNeZero
noncomputable def nativeMean : ℂ :=
  allocatedSlicedNativeEvalMean B U b S W slice.path.base slice.path.noise physicalN
    (slice.path.physicalPolynomial originalpoly) slice.principalLength slice.principalStep
    slice.principalStart slice.principalInside slice.principalLength_pos slice.kernelLength
    slice.kernelLength_two slice.kernelStart slice.step slice.kernelSupport activeH activeStart
    (fun j => slice.activeLength_two s.hδslice j.1 j.2) (fun j => slice.activeSupport j.1 j.2)

variable (gridVolume : ℝ) (hVpos : 0 < gridVolume)

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : slice.path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
variable {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
variable (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
variable (nativeCoeff : Findex → ℂ) (δnative : ℝ)
variable (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hp : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖((forecastGeometricJacobian (X := X) (I := I) U b R S.value gridVolume τ : ℝ) : ℂ) *
    forecastLawDensityPhysicalTarget B U b S slice.principalLaw (slice.density s.hBactive)
      (allocatedShortIntegerSelection U b S.value) slice.path.sample slice.path.commonTuple
      (fun _ : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S) =>
        slice.path.referenceInputLaw)
      (fun y => integerLongPolynomialOutput slice.path.referencePolynomial
        (fun k => (y (Prod.fst k) (Prod.snd k) : ℤ)) slice.path.referenceModulus)
      slice.path.referenceModulus gridVolume slice.path.base physicalN τ o hb bW poly hp u -
    ∑ i, nativeCoeff i * (F i).eval physicalN poly u‖ ≤ δnative)
variable {Pambient Eprec Rrank M : ℝ} (hPambient : 0 ≤ Pambient) (hEprec : 0 ≤ Eprec)
variable (hPP : s.P ≤ Pambient)
variable (hLip : ((Lip * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal coverCap) : ℝ≥0) : ℝ) ≤ Real.exp Pambient)
variable (hcoverF : ∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmodF : ∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmass : ∑ i, ‖nativeCoeff i‖ ≤ M)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {δgrid : ℝ} (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
variable (hgridmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
  forecastJointGridScale U b R S.value physicalN τ j ≤ δgrid)

noncomputable def comparisonError : ℝ :=
  allocatedSlicedPhysicalComparisonError B U b S ξ slice.kernelLength (t := t) activeH q
    (ε := ε) (η := η) (Kφ := Knative) +
  ((2 * δnative + M * Real.exp (-Eprec)) +
    allocatedSlicedPhysicalAmbientGridError (B := B) (U := U) (basis := b) (S := S) (E := Eout)
      (τ := τ) (ξ := ξ) (box := physicalN) (integerFrame := slice.path.noise)
      (HG := slice.kernelLength) (hHG := slice.kernelLength_two) (cG := slice.kernelStart)
      (stepG := slice.step) (hstepG := slice.step_pos) (e := spatialEquiv)
      (h0 := slice.analyticKernelDetFalse ξ) (h1 := slice.analyticKernelDetTrue ξ)
      (hδ := hδ) (o := o) (Lip := Lip) (cutoff := cutoff) (D := slice.decayConstant) (δgrid := δgrid))

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchPositivePowerInduction
namespace OAI

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators TensorProduct Classical

namespace ResidueBoxSlice

theorem polynomial_weighted_support {X : Type} {N : X → ℕ} {q : ℕ}
    (S : ResidueBoxSlice N q) (i : X) :
    S.polynomial i ∈ weightedSupportLE (fun _ : X => 1) 1 := by
  apply (mem_weightedSupportLE_iff _ _ _).mpr
  change (S.polynomial i).weightedTotalDegree (1 : X → ℕ) ≤ 1
  rw [MvPolynomial.weightedTotalDegree_one]
  exact S.polynomial_degree i

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformRelativePatchSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def SubquadraticPatchSource (k s : ℕ) (κ H₀ K q A₀ B D pmin Csrc : ℝ) : Prop :=
  let μ := levelCoefficient K * Real.log q
  let β := 1 - (gainExponent K - μ) / 2
  ∀ S : APFreeInterval k, pmin ≤ S.parameter →
    A₀ * S.parameter ^ β + Csrc ≤ Real.log (Real.log S.length) →
    ∃ (d M a q₀ : ℕ) (U : ℝ) (A : PolynomialPatch Unit s d),
      0 < q₀ ∧ (∀ n < M, a + q₀ * n < S.length) ∧ 1 ≤ U ∧
      Real.log S.length - U ≤ Real.log M ∧ (A.kernel.lip : ℝ) + 1 ≤ Real.exp U ∧
      Real.log ((d : ℝ) + 1) ≤ B * S.parameter ^ μ * Real.log (2 + S.parameter) ∧
      Real.log U ≤ D * S.parameter ^ (1 / 4 : ℝ) * Real.log (2 + S.parameter) ∧
      let G := κ * amplificationGain κ H₀ ⌊levelCoefficient K * Real.log S.parameter⌋₊ / 2
      Real.exp (-U) ≤ (𝔼 n : Fin M,
        (intervalIndicator S.points (a + q₀ * n.val) - G * S.density) *
          A.value (fun _ => (n.val : ℝ)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ActualFixedSpatialGoodPrimeDeletion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedReferencePrimeNeZero
attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedReferenceModulusNeZero
noncomputable def referenceLocalDensity
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus)
    (p : path.primes) : ℝ :=
  rationalOutputDensity
    (FiniteProbabilityWeights.uniform
      (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
        ZMod (p.val ^ path.exponent p.val)))
    (localPrimePowerIntegerPolynomialOutput p.val (path.exponent p.val) (path.prescribed p.val)
      (path.localReferencePolynomial raw) (path.origin p)) (p.val ^ path.exponent p.val)
    (fun j => ZMod.castHom (Finset.dvd_prod_of_mem
      (fun p : path.primes => p.val ^ path.exponent p.val) (Finset.mem_univ p))
      (ZMod (p.val ^ path.exponent p.val)) (β j))

noncomputable def retainedReferenceForecast {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) : ℝ :=
  gridVolume * inactive.fiberMean gridPoint z (fun i =>
    ∏ p ∈ path.referenceRetainedPrimes cutoff, path.referenceLocalDensity (raw i) β p)

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedModulusBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

namespace VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

attribute [local instance] retainedLabelDecidableEq

noncomputable def referenceRetainedCRTModulus (cutoff : ℕ) : ℕ :=
  ∏ p : path.referenceRetainedPrimes cutoff, p.val.val ^ path.exponent p.val.val

local instance smallReferencePrimeNeZero_ra22e53_1 : ∀ p : path.primes, NeZero p.val :=
  path.primeNeZero
local instance retainedFullReferenceModulusNeZero : NeZero path.referenceModulus :=
  ⟨path.referenceModulus_pos.ne'⟩

end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchTaggedBufferedScore
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial
variable {σ τ : Type*} {s d : ℕ}

namespace PolynomialPatch
variable (A : PolynomialPatch σ s d) (p : τ → ℕ)
  (f : MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ)

variable
  (hdegree : ∀ {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ},
    P ∈ weightedSupportLE (Sum.elim p A.weight) n →
    f P ∈ weightedSupportLE (Sum.elim p A.weight) n)

include hdegree in
theorem weightedSymbolicShearFullCenter_degree (i : Fin d) :
    A.symbolicShearFullCenter f i ∈
      weightedSupportLE (Sum.elim p A.weight) (A.weight i) := by
  apply (weightedSupportLE _ _).sub_mem (weightedSupportLE_X _ (Sum.inr i))
  apply hdegree
  apply polynomialHom_preserves_weightedDegree A.weight _ (rename Sum.inr) _
    (A.form.topResidualEquiv_degree (weightedSupportLE_X A.weight i))
  intro j
  rw [rename_X]
  exact weightedSupportLE_X _ (Sum.inr j)

noncomputable def weightedSymbolicShearForm : WeightedParameterSlots τ p d A.weight where
  center i := aeval (symbolicShearPrefixSubstitution i) (A.symbolicShearFullCenter f i)
  degree i := weightedSupportLE_aeval _ _ _
    (symbolicShearPrefixSubstitution_weighted_degree p A.weight i)
    (A.weightedSymbolicShearFullCenter_degree p f hdegree i)

noncomputable def weightedSymbolicShearPatch : WeightedParameterPatch τ p s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := A.weightedSymbolicShearForm p f hdegree
  kernel := A.kernel

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateAllKeptSliceLaw
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} {N : I → ℕ} {q : ℕ}

def keepTrueSlice (S : ResidueBoxSlice N q) :
    ResidueBoxSlice (fun i : {_i : I // True} => N i.val) q :=
  S.comap Subtype.val

def keepTrueParameterEquiv (S : ResidueBoxSlice N q) :
    (∀ i, Fin (S.length i)) ≃ (∀ i, Fin (S.keepTrueSlice.length i)) where
  toFun u i := u i.val
  invFun u i := u ⟨i, trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3.ResidueBoxSlice

end

end OAI
end


