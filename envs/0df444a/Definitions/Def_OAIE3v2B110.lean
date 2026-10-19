-- Prove2me | Definitions.Def_OAIE3v2B110
-- name    : OAIE3v2B110
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:38:48.562475+00:00
-- url     : https://prove2.me/theorems/edbbd1f8-d368-4217-be8f-5579967e89f3
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 112 of 311
-- statement:
--   Definitions bundle 112 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B087`, `OAIE3v2B088`, `OAIE3v2B089`, `OAIE3v2B090`, `OAIE3v2B092`, `OAIE3v2B093`, `OAIE3v2B298`, `OAIE3v2B095`, `OAIE3v2B096`, `OAIE3v2B097` of this split.
--
--   Modules: `Dynamics/ImageCoverBudget.lean`, `Dynamics/ProjectedAxisBudgets.lean`, `Dynamics/RationalLieQuotientBudget.lean`, `Estimates/AllocatedOriginalSampleQuadratureUniformBounds.lean`, `Estimates/CoefficientSliceEmbedding.lean`, `Estimates/CopiedLayerSpace.lean`, `Estimates/IntegralOrthogonalSection.lean`, `Estimates/JointRationalSpaceGenerators.lean`, `Estimates/QuotientInducedMark.lean`, `Estimates/RealifiedReconstruction.lean`, `Fourier/PolynomialWeightedCubeMajorArc.lean`, `Geometry/QuantitativeProjectedChart.lean`, `Geometry/RealChartReindexCoefficients.lean`, `Lattices/CubeResidueSupport.lean`, `Lattices/StandardLatticeCoordinates.lean`, `Linear/JointRationalSpaceDefiningMatrix.lean`, `Linear/SubmoduleQuotientSectionBasis.lean`, `Linear/TopSubspaceAdaptedBasis.lean`, `Polynomial/MajorWeightedDegreeTools.lean`, `Polynomial/PolynomialCoefficientNormalization.lean`, `Polynomial/PolynomialPatchShearOrbitConverse.lean`, `Polynomial/PolynomialScalarCubeLength.lean`, `Polynomial/PolynomialShearFactorialIntegrality.lean`, `Polynomial/PolynomialShearParameterBudget.lean`, `Polynomial/PolynomialSymbolicShearWeightedDegree.lean`, `Probability/CylinderJointMass.lean`, `Sampling/PatchKernelGridBudget.lean`.
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
import Definitions.Def_OAIE3v2B093
import Definitions.Def_OAIE3v2B298
import Definitions.Def_OAIE3v2B095
import Definitions.Def_OAIE3v2B096
import Definitions.Def_OAIE3v2B097

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3


open scoped BigOperators

theorem scalarCubeResidueWeights_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) (f : IntegerScalarCubeBox I L → ℝ) :
    (scalarCubeResidueWeights I L M hL m r hm hmM hsize).mean f =
      𝔼 x : ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r), f x := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  exact FiniteProbabilityWeights.uniform_condition_condition_mean _ _
    (integerScalarCubeReference_mass_pos I L hL)
    (scalarCubeResidue_mass_pos I L M hL m r hm hmM hsize) f

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorWeightedDegreeTools
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ}

theorem triangularPolynomialEquiv_X (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i)) (i : Fin d) :
    triangularPolynomialEquiv w Q hQ (X i) = X i + rename (earlierSlot i) (Q i) :=
  (Classical.choose_spec (exists_triangularPolynomialEquiv w Q hQ)).1 i

theorem triangularPolynomialEquiv_inverse_degree (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i))
    {m : ℕ} {p : MvPolynomial (Fin d) R} (hp : p ∈ weightedSupportLE w m) :
    (triangularPolynomialEquiv w Q hQ).symm p ∈ weightedSupportLE w m :=
  (Classical.choose_spec (exists_triangularPolynomialEquiv w Q hQ)).2.2 m p hp

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {d : ℕ}

theorem exists_triangularPolynomialEquiv_prefix_mass (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) ℝ)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i))
    {M : ℝ} (hM : 0 ≤ M) (hQM : ∀ i, realPolynomialMass (rename (earlierSlot i) (Q i)) ≤ M) (n : ℕ) :
    n ≤ d → ∃ E : MvPolynomial (Fin d) ℝ ≃ₐ[ℝ] MvPolynomial (Fin d) ℝ,
      (∀ i, E (X i) = if i.val < n then X i + rename (earlierSlot i) (Q i) else X i) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E p ∈ weightedSupportLE w m) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E.symm p ∈ weightedSupportLE w m) ∧
      (∀ m p, p ∈ weightedSupportLE w m →
        realPolynomialMass (E.symm p) ≤ realPolynomialMass p * (1 + M) ^ (m * n)) := by
  classical
  induction n with
  | zero =>
      intro _
      refine ⟨AlgEquiv.refl, ?_, ?_, ?_, ?_⟩
      · intro i
        rw [if_neg (Nat.not_lt_zero _)]
        rfl
      · intro m p hp
        exact hp
      · intro m p hp
        exact hp
      · intro m p hp
        change realPolynomialMass p ≤ realPolynomialMass p * (1 + M) ^ (m * 0)
        simp only [Nat.mul_zero, pow_zero, mul_one, le_refl]
  | succ n ih =>
      intro hn
      obtain ⟨E, hE, hEdeg, hEinv, hEmass⟩ := ih (Nat.le_of_succ_le hn)
      let k : Fin d := ⟨n, Nat.lt_of_succ_le hn⟩
      let H := coordinateShearEquiv k (earlierSlot k) (earlierSlot_ne_self k) (Q k)
      have hHself : H (X k) = X k + rename (earlierSlot k) (Q k) := by
        change coordinateShearHom k (earlierSlot k) (Q k) (X k) = _
        rw [coordinateShearHom_X, Function.update_self]
      have hHfix (i : Fin d) (hi : i ≠ k) : H (X i) = X i := by
        change coordinateShearHom k (earlierSlot k) (Q k) (X i) = _
        rw [coordinateShearHom_X, Function.update_of_ne hi]
      refine ⟨E.trans H, ?_, ?_, ?_, ?_⟩
      · intro i
        rw [AlgEquiv.trans_apply, hE i]
        by_cases hik : i = k
        · subst i
          rw [if_neg (by change ¬ n < n; omega),
            if_pos (by change n < n + 1; omega)]
          exact hHself
        · by_cases hi : i.val < n
          · have hfix : H (rename (earlierSlot i) (Q i)) = rename (earlierSlot i) (Q i) := by
              change coordinateShearHom k (earlierSlot k) (Q k) (rename (earlierSlot i) (Q i)) = _
              apply coordinateShearHom_rename
              intro j hj
              have hv := congrArg Fin.val hj
              have hji := j.isLt
              change j.val = n at hv
              omega
            rw [if_pos hi, if_pos (by omega), map_add, hHfix i hik, hfix]
          · have hne : i.val ≠ n := by
              intro he
              exact hik (Fin.ext he)
            rw [if_neg hi, if_neg (by omega), hHfix i hik]
      · intro m p hp
        change coordinateShearHom k (earlierSlot k) (Q k) (E p) ∈ weightedSupportLE w m
        exact coordinateShearHom_degree w k (earlierSlot k) (Q k) (hQ k) (hEdeg m p hp)
      · intro m p hp
        change E.symm (H.symm p) ∈ weightedSupportLE w m
        apply hEinv
        change coordinateShearHom k (earlierSlot k) (-Q k) p ∈ weightedSupportLE w m
        apply coordinateShearHom_degree w k (earlierSlot k) (-Q k) _ hp
        simpa only [map_neg] using (weightedSupportLE w (w k)).neg_mem (hQ k)
      · intro m p hp
        have hHp : H.symm p ∈ weightedSupportLE w m := by
          change coordinateShearHom k (earlierSlot k) (-Q k) p ∈ weightedSupportLE w m
          apply coordinateShearHom_degree w k (earlierSlot k) (-Q k) _ hp
          simpa only [map_neg] using (weightedSupportLE w (w k)).neg_mem (hQ k)
        have hHm : realPolynomialMass (H.symm p) ≤ realPolynomialMass p * (1 + M) ^ m :=
          coordinateShearEquiv_inverse_mass k (earlierSlot k) (earlierSlot_ne_self k) (Q k)
            hM (hQM k) (totalDegree_le_of_positive_weightedSupport w hw hp)
        change realPolynomialMass (E.symm (H.symm p)) ≤ realPolynomialMass p * (1 + M) ^ (m * (n + 1))
        calc
          _ ≤ realPolynomialMass (H.symm p) * (1 + M) ^ (m * n) := hEmass m (H.symm p) hHp
          _ ≤ (realPolynomialMass p * (1 + M) ^ m) * (1 + M) ^ (m * n) :=
            mul_le_mul_of_nonneg_right hHm (pow_nonneg (by linarith) _)
          _ = realPolynomialMass p * (1 + M) ^ (m * (n + 1)) := by
            rw [mul_assoc, ← pow_add, show m + m * n = m * (n + 1) by ring]

theorem triangularPolynomialEquiv_inverse_mass (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) ℝ)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i))
    {M : ℝ} (hM : 0 ≤ M) (hQM : ∀ i, realPolynomialMass (rename (earlierSlot i) (Q i)) ≤ M)
    {n : ℕ} {P : MvPolynomial (Fin d) ℝ} (hP : P ∈ weightedSupportLE w n) :
    realPolynomialMass ((triangularPolynomialEquiv w Q hQ).symm P) ≤
      realPolynomialMass P * (1 + M) ^ (n * d) := by
  obtain ⟨E, hE, _, _, hmass⟩ :=
    exists_triangularPolynomialEquiv_prefix_mass w hw Q hQ hM hQM d le_rfl
  have he : E.toAlgHom = (triangularPolynomialEquiv w Q hQ).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    change E (X i) = triangularPolynomialEquiv w Q hQ (X i)
    rw [hE, triangularPolynomialEquiv_X, if_pos i.isLt]
  have heq : E = triangularPolynomialEquiv w Q hQ :=
    AlgEquiv.ext (fun P => DFunLike.congr_fun he P)
  rw [← heq]
  exact hmass n P hP

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientNormalization
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

namespace PolynomialSlots

variable {d : ℕ} {w : Fin d → ℕ}

theorem sub_topPart_lower (A : PolynomialSlots σ d w) (i : Fin d) :
    A.center i - A.topPart.center i ∈ weightedSupportLT (patchSlotWeight w i) (w i) := by
  apply weightedTopPart_remainder_lt
  apply weightedSupportLE_of_weight_le _ (A.degree i)
  intro a
  cases a <;> simp [patchSlotWeight, patchVariableWeight]

theorem topPart_parameter_exponent_zero (A : PolynomialSlots σ d w) (i : Fin d)
    (a : (σ ⊕ Fin i.val) →₀ ℕ) (ha : (A.topPart.center i).coeff a ≠ 0) (j : σ) :
    a (Sum.inl j) = 0 := by
  have hs : a ∈ (weightedHomogeneousComponent (patchSlotWeight w i) (w i)
      (A.center i)).support := MvPolynomial.mem_support_iff.mpr ha
  rw [support_weightedHomogeneousComponent] at hs
  obtain ⟨hA, htop⟩ := Finset.mem_filter.mp hs
  have hdegree : Finsupp.weight (patchVariableWeight w i) a ≤ w i := A.degree i hA
  rw [patchVariableWeight_split, finsupp_weight_add_function, htop] at hdegree
  have hzero : Finsupp.weight (patchParameterWeight i) a = 0 := by omega
  have hle := Finsupp.le_weight (patchParameterWeight (σ := σ) i)
    (s := Sum.inl j) (by decide : (1 : ℕ) ≠ 0) a
  rw [hzero] at hle
  exact Nat.eq_zero_of_le_zero hle

end PolynomialSlots

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] {d : ℕ}

theorem slotPolynomialLift_degree (v : σ → ℕ) (w : Fin d → ℕ) (i : Fin d)
    {P : MvPolynomial (σ ⊕ Fin i.val) R} {n : ℕ}
    (hP : P ∈ weightedSupportLE (Sum.elim v (fun j => w (earlierSlot i j))) n) :
    slotPolynomialLift i P ∈ weightedSupportLE (Sum.elim v w) n := by
  apply polynomialHom_preserves_weightedDegree _ _ (rename (Sum.map id (earlierSlot i))) _ hP
  intro a
  rw [rename_X]
  cases a with
  | inl j => exact weightedSupportLE_X (Sum.elim v w) (Sum.inl j)
  | inr j => exact weightedSupportLE_X (Sum.elim v w) (Sum.inr (earlierSlot i j))

namespace PolynomialSlots

variable {w : Fin d → ℕ}

theorem topPart_aeval_independent {S : Type*} [CommRing S] [Algebra ℝ S]
    (A : PolynomialSlots σ d w) (i : Fin d) (t u : σ → S) (b : Fin i.val → S) :
    aeval (Sum.elim t b) (A.topPart.center i) =
      aeval (Sum.elim u b) (A.topPart.center i) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def]
  apply MvPolynomial.eval₂_congr
  intro v a hv ha
  cases v with
  | inl j => exact ((Finsupp.mem_support_iff.mp hv)
      (A.topPart_parameter_exponent_zero i a ha j)).elim
  | inr j => rfl

theorem topPart_lift_specialize (A : PolynomialSlots σ d w) (i : Fin d) :
    slotPolynomialLift i (A.topPart.center i) =
      rename Sum.inr (rename (earlierSlot i) (A.topPart.specializeCenter 0 i)) := by
  let b : Fin i.val → MvPolynomial (σ ⊕ Fin d) ℝ := fun j => X (Sum.inr (earlierSlot i j))
  have hcomp : (rename (R := ℝ) (Sum.inr : Fin d → σ ⊕ Fin d)).comp
      ((rename (earlierSlot i)).comp (aeval (Sum.elim (fun _ : σ => (0 : MvPolynomial (Fin i.val) ℝ)) X))) =
      aeval (Sum.elim (fun _ : σ => (0 : MvPolynomial (σ ⊕ Fin d) ℝ)) b) := by
    apply MvPolynomial.algHom_ext
    intro a
    cases a <;> simp [b]
  have he := congrArg (fun F : MvPolynomial (σ ⊕ Fin i.val) ℝ →ₐ[ℝ]
      MvPolynomial (σ ⊕ Fin d) ℝ => F (A.topPart.center i)) hcomp
  simp only [AlgHom.comp_apply] at he
  have hs : A.topPart.specializeCenter 0 i =
      aeval (Sum.elim (fun _ : σ => (0 : MvPolynomial (Fin i.val) ℝ)) X) (A.topPart.center i) := by
    simp only [specializeCenter, Pi.zero_apply, map_zero]
  rw [hs, he, slotPolynomialLift, MvPolynomial.rename_eq_aeval]
  have hinput : (X : σ ⊕ Fin d → MvPolynomial (σ ⊕ Fin d) ℝ) ∘
      Sum.map id (earlierSlot i) = Sum.elim (fun a => X (Sum.inl a)) b := by
    funext a
    cases a <;> rfl
  rw [hinput]
  exact A.topPart_aeval_independent i _ _ b

end PolynomialSlots

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolicShearWeightedDegree
namespace OAI

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem residualCoordinate_degree (A : PolynomialSlots σ d w) (i : Fin d) :
    A.residualCoordinate i ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) (w i) :=
  (weightedSupportLE _ _).sub_mem (weightedSupportLE_X _ (Sum.inr i))
    (slotPolynomialLift_degree (fun _ => 1) w i (A.degree i))

theorem residualCoordinate_slot_degree (A : PolynomialSlots σ d w) (i : Fin d) :
    A.residualCoordinate i ∈ weightedSupportLE (Sum.elim (fun _ : σ => 0) w) (w i) := by
  apply weightedSupportLE_of_weight_le _ (A.residualCoordinate_degree i)
  intro a
  cases a <;> simp

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem topResidualEquiv_X (A : PolynomialSlots σ d w) (i : Fin d) :
    A.topResidualEquiv (X i) = X i - rename (earlierSlot i) (A.topPart.specializeCenter 0 i) := by
  rw [topResidualEquiv, triangularPolynomialEquiv_X, map_neg, ← sub_eq_add_neg]

theorem topResidualEquiv_inverse_degree (A : PolynomialSlots σ d w)
    {n : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p ∈ weightedSupportLE w n) :
    A.topResidualEquiv.symm p ∈ weightedSupportLE w n :=
  triangularPolynomialEquiv_inverse_degree w _ A.topResidualShift_degree hp

theorem topResidualEquiv_lift (A : PolynomialSlots σ d w) :
    (rename (Sum.inr : Fin d → σ ⊕ Fin d)).comp A.topResidualEquiv.toAlgHom =
      A.topPart.residualHom := by
  apply MvPolynomial.algHom_ext
  intro i
  change rename Sum.inr (A.topResidualEquiv (X i)) = A.topPart.residualHom (X i)
  rw [topResidualEquiv_X, map_sub, rename_X, residualHom_X, residualCoordinate,
    topPart_lift_specialize]

noncomputable def loweringHom (A : PolynomialSlots σ d w) :
    MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (σ ⊕ Fin d) ℝ :=
  A.residualHom.comp A.topResidualEquiv.symm.toAlgHom

theorem loweringHom_comp_top (A : PolynomialSlots σ d w) :
    A.loweringHom.comp A.topResidualEquiv.toAlgHom = A.residualHom := by
  apply AlgHom.ext
  intro p
  change A.residualHom (A.topResidualEquiv.symm (A.topResidualEquiv p)) = A.residualHom p
  rw [AlgEquiv.symm_apply_apply]

theorem loweringHom_degree (A : PolynomialSlots σ d w)
    {n : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p ∈ weightedSupportLE w n) :
    A.loweringHom p ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n := by
  change A.residualHom (A.topResidualEquiv.symm p) ∈ _
  apply polynomialHom_preserves_weightedDegree w _ A.residualHom _
    (A.topResidualEquiv_inverse_degree hp)
  intro i
  rw [residualHom_X]
  exact A.residualCoordinate_degree i

end Erdos3.PolynomialSlots

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ}

namespace PolynomialSlots

variable {w : Fin d → ℕ}

noncomputable def loweringAtHom (A : PolynomialSlots σ d w) (t : σ → ℝ) :
    MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ :=
  (patchParameterSpecialization t).comp A.loweringHom

end PolynomialSlots

end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def symbolicShearHom (A : PolynomialSlots σ d w) :
    MvPolynomial (σ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (σ ⊕ Fin d) ℝ :=
  aeval (Sum.elim (fun a => X (Sum.inl a)) (fun i => A.loweringHom (X i)))

theorem symbolicShearHom_parameter (A : PolynomialSlots σ d w) (a : σ) :
    A.symbolicShearHom (X (Sum.inl a)) = X (Sum.inl a) := by
  simp only [symbolicShearHom, aeval_X, Sum.elim_inl]

theorem symbolicShearHom_slot (A : PolynomialSlots σ d w) (i : Fin d) :
    A.symbolicShearHom (X (Sum.inr i)) = A.loweringHom (X i) := by
  simp only [symbolicShearHom, aeval_X, Sum.elim_inr]

theorem symbolicShearHom_degree (A : PolynomialSlots σ d w)
    {n : ℕ} {P : MvPolynomial (σ ⊕ Fin d) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n) :
    A.symbolicShearHom P ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n := by
  apply weightedSupportLE_aeval _ _ _ _ hP
  intro j
  cases j with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr i => exact A.loweringHom_degree (weightedSupportLE_X w i)

theorem symbolicShearHom_specialization (A : PolynomialSlots σ d w) (t : σ → ℝ)
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t (A.symbolicShearHom P) =
      A.loweringAtHom t (patchParameterSpecialization t P) := by
  have h : (patchParameterSpecialization t).comp A.symbolicShearHom =
      (A.loweringAtHom t).comp (patchParameterSpecialization t) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | inl a =>
      simp [AlgHom.comp_apply, symbolicShearHom_parameter, patchParameterSpecialization,
        loweringAtHom]
    | inr i =>
      change patchParameterSpecialization t (A.symbolicShearHom (X (Sum.inr i))) =
        A.loweringAtHom t (patchParameterSpecialization t (X (Sum.inr i)))
      rw [symbolicShearHom_slot, patchParameterSpecialization_X_slot]
      rfl
  exact DFunLike.congr_fun h P

theorem symbolicShearDifference_pow_degree (A : PolynomialSlots σ d w) (k : ℕ)
    {n : ℕ} {P : MvPolynomial (σ ⊕ Fin d) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n) :
    (polynomialHomDifference A.symbolicShearHom ^ k) P ∈
      weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (weightedSupportLE _ n).sub_mem (A.symbolicShearHom_degree ih) ih

end Erdos3.PolynomialSlots

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearFactorialIntegrality
namespace OAI

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def symbolicLogSlot (A : PolynomialSlots σ d w) (i : Fin d) :
    MvPolynomial (σ ⊕ Fin d) ℝ :=
  ∑ k ∈ Finset.range (w i + 1), ((-1 : ℚ) ^ (k + 1) / k) •
    (polynomialHomDifference A.symbolicShearHom ^ k) (X (Sum.inr i))

theorem symbolicLogSlot_degree (A : PolynomialSlots σ d w) (i : Fin d) :
    A.symbolicLogSlot i ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) (w i) := by
  apply (weightedSupportLE _ _).sum_mem
  intro k hk
  exact (weightedSupportLE (Sum.elim (fun _ : σ => 1) w) (w i)).restrictScalars ℚ |>.smul_mem _
    (A.symbolicShearDifference_pow_degree k (weightedSupportLE_X _ (Sum.inr i)))

end Erdos3.PolynomialSlots

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedReconstruction
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ}

theorem exists_bounded_filtered_section
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {k | j ≤ τ k}))
    (φ : L →ₗ[ℚ] M)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) :
    ∃ S : M →ₗ[ℚ] L,
      Function.RightInverse S φ ∧
      (∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) ∧
      ∀ i k, RationalHeightLE (b.repr (S (c k)) i)
        (rationalKernelHeight (Fintype.card κ) H) := by
  classical
  have lifts (k : κ) : ∃ x : L,
      x ∈ F.layer (τ k) ∧ φ x = c k ∧
        ∀ i, RationalHeightLE (b.repr x i) (rationalKernelHeight (Fintype.card κ) H) := by
    let P := basisCoordinateProjection b {i | τ k ≤ ω i}
    have hmasked : ∀ a i, RationalHeightLE (c.repr ((φ.comp P) (b i)) a) H := by
      intro a i
      change RationalHeightLE (c.repr (φ (basisCoordinateProjection b {i | τ k ≤ ω i} (b i))) a) H
      rw [basisCoordinateProjection_basis]
      split_ifs
      · exact hentries a i
      · simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
    obtain ⟨T, hT, hTH⟩ := exists_bounded_linear_image_section b c (φ.comp P) hH hmasked
    have hck : c k ∈ G.layer (τ k) := by
      rw [hG]
      exact Submodule.subset_span ⟨k, (show τ k ≤ τ k from le_rfl), rfl⟩
    obtain ⟨y, hy, hφy⟩ := hsurj (τ k) (c k) hck
    have hPy : P y = y := by
      apply basisCoordinateProjection_eq_self
      rwa [← hF]
    have himage : (φ.comp P) y = c k := by
      change φ (P y) = c k
      rw [hPy, hφy]
    have hright : (φ.comp P) (T (c k)) = c k := by
      have ht := congrArg (fun A : L →ₗ[ℚ] M => A y) hT
      change (φ.comp P) (T ((φ.comp P) y)) = (φ.comp P) y at ht
      simpa only [himage] using ht
    refine ⟨P (T (c k)), ?_, hright, ?_⟩
    · rw [hF]
      exact basisCoordinateProjection_mem_span b _ _
    · intro i
      change RationalHeightLE
        (b.repr (basisCoordinateProjection b {i | τ k ≤ ω i} (T (c k))) i) _
      rw [basisCoordinateProjection_repr]
      split_ifs
      · exact hTH i k
      · exact rationalHeightLE_zero (rationalKernelHeight_pos _ hH)
  choose v hmem hright hheight using lifts
  let S := c.constr ℚ v
  have hS (k : κ) : S (c k) = v k := c.constr_basis ℚ v k
  refine ⟨S, ?_, ?_, ?_⟩
  · have hcomp : φ.comp S = LinearMap.id := by
      apply c.ext
      intro k
      change φ (S (c k)) = c k
      rw [hS, hright]
    intro y
    exact congrArg (fun A : M →ₗ[ℚ] M => A y) hcomp
  · intro j y hy
    have hle : G.layer j ≤ (F.layer j).comap S := by
      rw [hG]
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      change S (c k) ∈ F.layer j
      rw [hS]
      exact F.antitone hk (hmem k)
    exact hle hy
  · intro i k
    rw [hS]
    exact hheight k i

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ImageCoverBudget
namespace OAI

section

namespace Erdos3

theorem exists_image_cover_reconstruction_budget (K C : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ p : ℝ, 0 ≤ p →
      let q := 2 * p + imageLatticeLogBudget K p
      q ≤ (p + N) ^ N ∧ p * (p + imageLatticeLogBudget K p) ≤ (p + N) ^ N ∧
        (q + C) ^ C ≤ (p + N) ^ N := by
  let L : Polynomial ℕ := Polynomial.C K + (Polynomial.X + 2) ^ 4 +
    2 * Polynomial.X + (Polynomial.X + 2) ^ 9
  let q : Polynomial ℕ := 2 * Polynomial.X + L
  let P : Polynomial ℕ := q + Polynomial.X * (Polynomial.X + L) + (q + Polynomial.C C) ^ C
  obtain ⟨N, hN, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨N, hN, ?_⟩
  intro p hp
  have hlog := imageLatticeLogBudget_nonneg K hp
  have hq : 0 ≤ 2 * p + imageLatticeLogBudget K p := by positivity
  have hidx : 0 ≤ p * (p + imageLatticeLogBudget K p) := by positivity
  have hcost : 0 ≤ (2 * p + imageLatticeLogBudget K p + C) ^ C := by positivity
  have heq : P.eval₂ (Nat.castRingHom ℝ) p = (2 * p + imageLatticeLogBudget K p) +
      p * (p + imageLatticeLogBudget K p) + (2 * p + imageLatticeLogBudget K p + C) ^ C := by
    simp [P, q, L, imageLatticeLogBudget, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  have hb := hbound p hp
  rw [heq] at hb
  dsimp only
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IntegralOrthogonalSection
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem latticeSection_orthogonal_full (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hintegral : Λ ≤ euclideanDualLattice Λ)
    (W : Submodule ℝ E) [IsZLattice ℝ (latticeSection Λ W)] :
    IsZLattice ℝ (latticeSection Λ Wᗮ) := by
  let B := Free.chooseBasis ℤ (latticeSection Λ W)
  let b := B.ofZLatticeBasis ℝ (latticeSection Λ W)
  let π : E →ₗ[ℝ] (Free.ChooseBasisIndex ℤ (latticeSection Λ W) → ℝ) :=
    LinearMap.pi (fun i => innerₗ E (b i).val)
  have hπ : ∀ x ∈ Λ, π x ∈ realIntegerGrid := by
    intro x hx
    have h : ∀ i, ∃ n : ℤ, (n : ℝ) = π x i := by
      intro i
      have hi : (b i : E) ∈ Λ := by
        have hi₀ : (B i).val.val ∈ Λ := (B i).property
        simpa only [b, Basis.ofZLatticeBasis_apply] using hi₀
      obtain ⟨n, hn⟩ := (mem_euclideanDualLattice Λ (b i).val).mp (hintegral hi) x hx
      exact ⟨n, hn.symm⟩
    choose z hz using h
    exact ⟨z, funext hz⟩
  have hk : LinearMap.ker π = Wᗮ := ker_basis_inner_eq_orthogonal W b
  have hfull := latticeKernel_full Λ π hπ
  have hsection : IsZLattice ℝ (latticeSection Λ (LinearMap.ker π)) := hfull
  exact (congrArg (fun V : Submodule ℝ E => IsZLattice ℝ (latticeSection Λ V)) hk).mp hsection

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointRationalSpaceGenerators
namespace OAI

section

namespace Erdos3

open scoped Matrix

namespace VectorPolynomial

theorem exists_jointRationalSpace_generators {J C V : Type*}
    [Fintype J] [Fintype C] [Fintype V]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) {H R : ℕ}
    (hH : 1 ≤ H) (hR : 1 ≤ R)
    (hB : ∀ i j, RationalHeightLE (B i j) H) (hA : ∀ v j, RationalHeightLE (A v j) R) :
    ∃ P : Matrix J J ℚ,
      (∀ i j, RationalHeightLE (P i j)
        (jointSpaceGeneratorHeight (Fintype.card J) (Fintype.card C) (Fintype.card V) H R)) ∧
      LinearMap.range (Matrix.of (fun i j => (P i j : ℝ))).mulVecLin = jointRationalSpace B A := by
  obtain ⟨Q, hQ, hQker⟩ := exists_real_span_defining_matrix B hH hB
  let A' : Matrix (J ⊕ V) J ℚ := Matrix.of (fun v j => Sum.elim (fun i => Q i j) (fun v => A v j) v)
  have hA' : ∀ v j, RationalHeightLE (A' v j) (max (imageDefiningHeight (Fintype.card C) (Fintype.card J) H) R) := by
    intro v j
    cases v with
    | inl i => exact (hQ i j).mono (le_max_left _ _)
    | inr v => exact (hA v j).mono (le_max_right _ _)
  obtain ⟨P, hP, hPker⟩ := exists_real_kernel_generators A' (hR.trans (le_max_right _ _)) hA'
  refine ⟨P, ?_, hPker.trans ?_⟩
  · simpa only [Fintype.card_sum, jointSpaceGeneratorHeight] using hP
  · ext x
    change LinearMap.ker (Matrix.of (fun i j => (Q i j : ℝ))).mulVecLin =
      LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin at hQker
    change (Matrix.of (fun v j => (A' v j : ℝ)) *ᵥ x = 0) ↔
      x ∈ LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin ∧
      Matrix.of (fun v j => (A v j : ℝ)) *ᵥ x = 0
    rw [← hQker]
    change (Matrix.of (fun v j => (A' v j : ℝ)) *ᵥ x = 0) ↔
      (Matrix.of (fun i j => (Q i j : ℝ)) *ᵥ x = 0) ∧
      Matrix.of (fun v j => (A v j : ℝ)) *ᵥ x = 0
    constructor
    · intro hx
      exact ⟨funext (fun i => congrFun hx (.inl i)), funext (fun v => congrFun hx (.inr v))⟩
    · rintro ⟨hQx, hAx⟩
      ext v
      cases v with
      | inl i => exact congrFun hQx i
      | inr v => exact congrFun hAx v

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {J : Type*} [Fintype J]

instance projectedIntegerLattice_discrete (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    DiscreteTopology (projectedIntegerLattice W) := by
  let : IsZLattice ℝ (latticeSection (standardEuclideanLattice J) Wᗮ) :=
    latticeSection_orthogonal_full (standardEuclideanLattice J)
      (by rw [standardEuclideanLattice_self_dual]) W
  let : IsZLattice ℝ (latticeSection (euclideanDualLattice (standardEuclideanLattice J)) Wᗮ) := by
    constructor
    change span ℝ {x : Wᗮ | x.val ∈ euclideanDualLattice (standardEuclideanLattice J)} = ⊤
    rw [standardEuclideanLattice_self_dual]
    exact IsZLattice.span_top (K := ℝ) (L := latticeSection (standardEuclideanLattice J) Wᗮ)
  exact orthogonalLatticeImage_discrete (standardEuclideanLattice J) Wᗮ

instance projectedIntegerLattice_full (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    IsZLattice ℝ (projectedIntegerLattice W) := by
  let : DiscreteTopology (orthogonalLatticeImage (standardEuclideanLattice J) Wᗮ) :=
    projectedIntegerLattice_discrete W
  exact orthogonalLatticeImage_full (standardEuclideanLattice J) Wᗮ

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory

theorem projectedIntegerLattice_covolume {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) *
      ZLattice.covolume (projectedIntegerLattice W) = 1 := by
  have hW : Wᗮᗮ = W := W.orthogonal_orthogonal
  let : DiscreteTopology (orthogonalLatticeImage (standardEuclideanLattice J) Wᗮ) :=
    projectedIntegerLattice_discrete W
  let : IsZLattice ℝ (orthogonalLatticeImage (standardEuclideanLattice J) Wᗮ) :=
    projectedIntegerLattice_full W
  let : IsZLattice ℝ (latticeSection (standardEuclideanLattice J) Wᗮᗮ) :=
    (congrArg (fun V : Submodule ℝ (EuclideanSpace ℝ J) =>
      IsZLattice ℝ (latticeSection (standardEuclideanLattice J) V)) hW).mpr inferInstance
  have h := orthogonalLattice_covolume (standardEuclideanLattice J) Wᗮ
  have hc := congrArg (fun V : Submodule ℝ (EuclideanSpace ℝ J) =>
    ZLattice.covolume (latticeSection (standardEuclideanLattice J) V)) hW
  rw [hc, standardEuclideanLattice_covolume] at h
  exact h.symm

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped Matrix NNReal

variable {J R I : Type*} [Fintype J] [Fintype R]

theorem projectedIntegerLattice_norm_inv_le_of_rational_kernel
    (Q : Matrix R J ℚ) (W : Submodule ℝ (J → ℝ))
    (hW : LinearMap.ker (Matrix.mulVecLin (fun r j => (Q r j : ℝ))) = W)
    {H : ℕ} (hQ : ∀ r j, RationalHeightLE (Q r j) H)
    {z : (euclideanSubspace W)ᗮ}
    (hz : z ∈ projectedIntegerLattice (euclideanSubspace W)) (hne : z ≠ 0) :
    ‖z‖⁻¹ ≤ rationalKernelAxisBound Q H := by
  classical
  obtain ⟨x, hx, hxz⟩ := hz
  change (euclideanSubspace W)ᗮ.orthogonalProjectionOnto x = z at hxz
  let y : EuclideanSpace ℝ J := x - z.val
  have hy : y ∈ euclideanSubspace W := by
    have h := (euclideanSubspace W)ᗮ.sub_starProjection_mem_orthogonal x
    rw [Submodule.orthogonal_orthogonal] at h
    simpa only [Submodule.starProjection_apply, hxz] using h
  have hQy : (fun r j => (Q r j : ℝ)) *ᵥ WithLp.ofLp y = 0 := by
    change WithLp.ofLp y ∈ W at hy
    rw [← hW] at hy
    exact hy
  have hxgrid : WithLp.ofLp x ∈ realDenominatorGrid 1 := by
    choose a ha using (mem_standardEuclideanLattice J x).mp hx
    refine ⟨a, ?_⟩
    ext j
    simpa only [Pi.smul_apply, Nat.cast_one, one_smul] using ha j
  have hQx : (fun r j => (Q r j : ℝ)) *ᵥ WithLp.ofLp x ≠ 0 := by
    intro hzero
    have hxW : x ∈ euclideanSubspace W := by
      change WithLp.ofLp x ∈ W
      rw [← hW]
      exact hzero
    have hproj : (euclideanSubspace W)ᗮ.orthogonalProjectionOnto x = 0 :=
      Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
        ((euclideanSubspace W).le_orthogonal_orthogonal hxW)
    exact hne (hxz.symm.trans hproj)
  have hsep : 1 ≤ rationalKernelAxisBound Q H *
      dist (WithLp.ofLp x) (WithLp.ofLp y) := by
    by_contra! hsmall
    apply hQx
    apply rational_matrix_kernel_separation Q (H : ℝ≥0)
      (fun r j => (hQ r j).abs_real_le) 1 (by decide)
      (WithLp.ofLp x) (WithLp.ofLp y) hxgrid hQy
    simpa only [Nat.mul_one, rationalKernelAxisBound, NNReal.coe_natCast] using hsmall
  have hdist : dist (WithLp.ofLp x) (WithLp.ofLp y) ≤ ‖z‖ := by
    rw [dist_eq_norm]
    have he : WithLp.ofLp x - WithLp.ofLp y = WithLp.ofLp z.val := by
      ext j
      change x j - (x j - z.val j) = z.val j
      ring
    rw [he]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
      (fun j => PiLp.norm_apply_le z.val j)
  have hbound : 1 ≤ rationalKernelAxisBound Q H * ‖z‖ :=
    hsep.trans (mul_le_mul_of_nonneg_left hdist (by
      unfold rationalKernelAxisBound
      positivity))
  exact (inv_le_iff_one_le_mul₀ (norm_pos_iff.mpr hne)).mpr hbound

theorem basisAxisScale_le_of_rational_kernel
    (Q : Matrix R J ℚ) (W : Submodule ℝ (J → ℝ))
    (hW : LinearMap.ker (Matrix.mulVecLin (fun r j => (Q r j : ℝ))) = W)
    {H : ℕ} (hQ : ∀ r j, RationalHeightLE (Q r j) H)
    (b : Basis I ℝ (euclideanSubspace W)ᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice (euclideanSubspace W))
    (i : I) :
    basisAxisScale b i ≤ ⌈rationalKernelAxisBound Q H⌉₊ := by
  apply Nat.ceil_mono
  apply projectedIntegerLattice_norm_inv_le_of_rational_kernel Q W hW hQ
  · rw [← hb]
    exact subset_span (Set.mem_range_self i)
  · exact b.ne_zero i

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

theorem jointRationalSpaceLattice_full
    {J C V : Type*} [Fintype J] [Fintype C] [Fintype V]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) {H R : ℕ}
    (hH : 1 ≤ H) (hR : 1 ≤ R)
    (hB : ∀ i j, RationalHeightLE (B i j) H) (hA : ∀ v j, RationalHeightLE (A v j) R) :
    IsZLattice ℝ (latticeSection (standardEuclideanLattice J)
      (euclideanSubspace (VectorPolynomial.jointRationalSpace B A))) := by
  obtain ⟨P, hP, hW⟩ := VectorPolynomial.exists_jointRationalSpace_generators B A hH hR hB hA
  exact rationalRangeLattice_full P _ hW hP

end Erdos3

end

section

namespace Erdos3

open Module Submodule BohrLattice.MinkowskiSecondBox
open scoped BigOperators

theorem exists_short_projected_integer_basis {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    let n := finrank ℝ Wᗮ
    ∃ b : Basis (Fin n) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∏ i, ‖b i‖) ≤ (n : ℝ) ^ n * minkowskiSecondConstant n *
        ZLattice.covolume (projectedIntegerLattice W) ∧
      ∀ i, ‖b i‖ ≤ (n : ℝ) * n.factorial * minkowskiSecondConstant n := by
  simpa only [mul_one] using exists_short_euclidean_lattice_basis
    (projectedIntegerLattice W) (stdOrthonormalBasis ℝ Wᗮ) (projectedIntegerGenerator W)
    (projectedIntegerGenerator_span W) (projectedIntegerGenerator_mem W)
    (projectedIntegerGenerator_norm_le W)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ProjectedAxisBudgets
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory BohrLattice.MinkowskiSecondBox
open scoped BigOperators

theorem exists_projected_basis_with_axis_budgets {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    let n := finrank ℝ Wᗮ
    ∃ b : Basis (Fin n) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∏ i, ‖b i‖) ≤ projectedAxisDefectBudget n * ZLattice.covolume (projectedIntegerLattice W) ∧
      ∀ i, ‖b i‖ ≤ projectedAxisNormBudget n := by
  let n := finrank ℝ Wᗮ
  obtain ⟨b, hb, hprod, hnorm⟩ := exists_short_projected_integer_basis W
  have hpow : (n : ℝ) ^ n ≤ ((n : ℝ) + 1) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (le_add_of_nonneg_right zero_le_one) n
  have hC := minkowskiSecondConstant_nonneg n
  refine ⟨b, hb, ?_, ?_⟩
  · exact hprod.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow hC)
      (ZLattice.covolume_pos (projectedIntegerLattice W) volume).le)
  · intro i
    exact (hnorm i).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Nat.cast_nonneg _)) hC)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RationalLieQuotientBudget
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_quotient_presentation_exp_height {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H : ℕ} (hHpos : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ D : Matrix (Fin d) ι ℚ, ∃ S : Matrix ι (Fin d) ℚ,
        LinearMap.ker D.mulVecLin = LinearMap.range A.mulVecLin ∧ D * S = 1 ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 7)) ∧
        ∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 45) ∧
          ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 45) := by
  obtain ⟨t, ht, d, hd, D, S, hker, hDS, hD, hS⟩ :=
    exists_bounded_quotient_presentation A hHpos hA
  have htp : (t : ℝ) ≤ p :=
    (show (t : ℝ) ≤ Fintype.card κ from by exact_mod_cast ht).trans hcols
  have hdp : (d : ℝ) ≤ p :=
    (show (d : ℝ) ≤ Fintype.card ι from by exact_mod_cast hd).trans hrows
  have hK := rationalKernelHeight_le_budget t H hp htp hH
  have hSbudget : (rationalSolveHeight d (rationalKernelHeight t H) : ℝ) ≤
      Real.exp ((p + 2) ^ 45) := by
    have hb := rationalSolveHeight_le_budget d (rationalKernelHeight t H)
      (by positivity : 0 ≤ (p + 2) ^ 7)
      (hdp.trans (le_power_budget hp (by decide : 1 ≤ 7))) hK
    exact exponential_budget_comp hp (by positivity) 7 5 le_rfl hb
  refine ⟨d, hd, D, S, hker, hDS, ?_, ?_⟩
  · intro i j
    constructor
    · exact (show ((D i j).num.natAbs : ℝ) ≤ rationalKernelHeight t H from
        by exact_mod_cast (hD i j).1).trans hK
    · exact (show ((D i j).den : ℝ) ≤ rationalKernelHeight t H from
        by exact_mod_cast (hD i j).2).trans hK
  · intro i j
    constructor
    · exact (show ((S i j).num.natAbs : ℝ) ≤ rationalSolveHeight d (rationalKernelHeight t H) from
        by exact_mod_cast (hS i j).1).trans hSbudget
    · exact (show ((S i j).den : ℝ) ≤ rationalSolveHeight d (rationalKernelHeight t H) from
        by exact_mod_cast (hS i j).2).trans hSbudget

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientInducedMark
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M]
  (I : LieIdeal ℚ L) (π : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, π x = 0)

namespace NilpotentLieFiltration

variable {s t u : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M u)

theorem quotientInducedMark_mem_layer
    (I : LieIdeal ℚ L) (hkill : F.layer (t + 1) ≤ I.toSubmodule)
    (π : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, π x = 0)
    (hπ : ∀ j, ∀ x ∈ F.layer j, π x ∈ G.layer j)
    (j : ℕ) (y : L ⧸ I) (hy : y ∈ (F.quotientLie I hkill).layer j) :
    quotientInducedMark I π hker y ∈ G.layer j := by
  obtain ⟨x, hx, rfl⟩ := hy
  exact hπ j x hx

end NilpotentLieFiltration
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

variable {σ τ : Type*}

namespace PolynomialSlots

variable {d : ℕ} {w : Fin d → ℕ}

theorem center_mass_le_of_normalized [Fintype σ] (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s)
    (hA : ∀ i α, |(A.center i).coeff α| ≤ 1 / 2) (i : Fin d) :
    realPolynomialMass (A.center i) ≤ ((s + 1) * (Fintype.card σ + d + 1) ^ s : ℕ) := by
  have hdegree : (A.center i).totalDegree ≤ s :=
    (totalDegree_le_of_positive_weightedSupport (patchVariableWeight w i) (by
      intro a
      cases a with
      | inl j => exact le_rfl
      | inr j => exact hpos (earlierSlot i j)) (A.degree i)).trans (hw i)
  have hmass : realPolynomialMass (A.center i) ≤ ((A.center i).support.card : ℝ) := by
    unfold realPolynomialMass
    calc
      _ ≤ ∑ _α ∈ (A.center i).support, (1 : ℝ) :=
        Finset.sum_le_sum (fun α _ => (hA i α).trans (by norm_num))
      _ = _ := by simp
  apply hmass.trans
  have hcard := polynomial_support_card_le (A.center i) hdegree
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  exact_mod_cast hcard.trans (Nat.mul_le_mul_left (s + 1)
    (Nat.pow_le_pow_left (by omega : Fintype.card σ + i.val + 1 ≤ Fintype.card σ + d + 1) s))

end PolynomialSlots
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget
namespace OAI

section

namespace Erdos3

theorem exists_natPolynomial_fixed_power_budget (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨(C + 1) * C, by nlinarith, ?_⟩
  intro p hp
  exact (hbound p hp).trans (shifted_power_le_fixed_base hp C hC)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

noncomputable def point (z : IntegerScalarCubeBox I d.length) : Option I → ℝ :=
  fun i => (z i : ℝ) / d.length

noncomputable def error (η : ℝ) : ℝ :=
  d.weightBound * scalarCubeResidueCutoffBudget I d.transitionBound d.radius d.length d.modulusBound +
    paddedResidueDensityCap I d.modulusBound *
      (((d.weightLipschitz : ℝ) + d.weightBound * scalarCubeCutoffLipschitzConstant I d.transitionBound d.radius) *
        d.mesh + d.weightBound * η)

end ScalarCubeLocalizationData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialScalarCubeLength
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ε W : ℝ}
    (h : ScalarCubePrimitiveBudget s A U) (hε : 0 < ε) (hε1 : ε ≤ 1) (hW : 1 ≤ W)
    (hlen : localizationLengthBudget U ε W ≤ s.length)

noncomputable def polynomialLocalizationData : ScalarCubeLocalizationData I := by
  have hU0 : 0 < U := by linarith [h.one_le]
  have hδ := localizationMesh_pos h.one_le hε
  have hbase : U ^ 2 ≤ (s.length : ℝ) :=
    (localizationLengthBudget_ge_square h.one_le hε hε1 hW).trans hlen
  have hgrid : 2 * scalarCubeGridBoundaryConstant I * s.modulusBound /
      volume.real (scalarCubeDomain I) ≤ s.length := by
    calc
      _ = (2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I)) * s.modulusBound := by ring
      _ ≤ U * U := mul_le_mul h.grid_le h.modulus_le (Nat.cast_nonneg _) hU0.le
      _ ≤ _ := by nlinarith
  have hδL : 2 * U * W ≤ localizationMesh U ε * s.length := by
    simpa only [localizationMesh_length h.one_le hε] using mul_le_mul_of_nonneg_left hlen hδ.le
  exact {
    length := s.length, modulusBound := s.modulusBound, length_pos := s.length_pos
    modulus := s.modulus, residue := s.residue, modulus_pos := s.modulus_pos
    modulus_le := s.modulus_le, size := s.size
    gridSmall := scalarCubeGrid_small_error_of_length I s.length_pos hgrid
    transitionBound := A, transition_lipschitz := hA
    radius := ⟨localizationRadius U ε, (localizationRadius_pos h.one_le hε).le⟩
    radius_pos := localizationRadius_pos h.one_le hε
    weight := s.weight, weightBound := s.weightBound, weightLipschitz := s.weightLipschitz
    weightBound_pos := s.weightBound_pos, weight_range := s.weight_range
    weight_lipschitz := s.weight_lipschitz, normalized := s.normalized
    mesh := localizationMesh U ε, mesh_pos := hδ
    mesh_le_one := localizationMesh_le_one h.one_le hε hε1
    meshLarge := by
      have hw := le_mul_of_one_le_right hU0.le hW
      nlinarith [h.modulus_le]
    margin := (mul_le_mul_of_nonneg_right h.dimension_le hδ.le).trans_lt
      (localizationMesh_margin h.one_le hε hε1) }

end NormalizedScalarCubeSource

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PolynomialWeightedCubeMajorArc
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {n : ℕ} {U ζ : ℝ}
    (h : ScalarCubePrimitiveBudget s A U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : localizedMajorArcLengthBudget n U ζ ≤ s.length)

noncomputable def majorArcLocalizationData : ScalarCubeLocalizationData I :=
  s.polynomialLocalizationData A hA h (localizationThreshold_pos h.one_le hζ (n + 1))
    (localizationThreshold_le_one h.one_le hζ hζ1 (n + 1))
    (by linarith [localizedMajorArcBudget_pos n h.one_le hζ]) hlen

end NormalizedScalarCubeSource
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuantitativeProjectedChart
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

theorem exists_normalized_projected_chart {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    let n := finrank ℝ Wᗮ
    let B := projectedAxisNormBudget n
    let D := projectedAxisDefectBudget n
    ∃ b : Basis (Fin n) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∀ i, 0 < basisAxisScale b i) ∧
      (∀ i, 1 ≤ ‖normalizedAxisBasis b i‖ ∧ ‖normalizedAxisBasis b i‖ ≤ B + 1) ∧
      (∀ x, ‖normalizedOrthogonalChart W b x‖ ≤
        (1 + (n : ℝ) * n.factorial * (B + 1) ^ (n - 1) * D) * ‖x‖) ∧
      (∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ (1 + (n : ℝ) * (B + 1)) * ‖p‖) ∧
      1 / ((n.factorial : ℝ) * (B + 1) ^ n) ≤
        ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) /
          (∏ i, (basisAxisScale b i : ℝ)) ∧
      ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) /
          (∏ i, (basisAxisScale b i : ℝ)) ≤ D := by
  let n := finrank ℝ Wᗮ
  let o := stdOrthonormalBasis ℝ Wᗮ
  obtain ⟨b, hspan, hprod, hnorm⟩ := exists_projected_basis_with_axis_budgets W
  have hprod' : (∏ i, ‖b i‖) ≤ projectedAxisDefectBudget n *
      ZLattice.covolume (span ℤ (Set.range b)) := by
    rw [hspan]
    exact hprod
  have hpair : ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) *
      ZLattice.covolume (span ℤ (Set.range b)) = 1 := by
    rw [hspan]
    exact projectedIntegerLattice_covolume W
  refine ⟨b, hspan, basisAxisScale_pos b, normalizedAxisBasis_norm_bounds b hnorm,
    ?_, ?_, ?_⟩
  · exact normalizedOrthogonalChart_norm_le W b o (projectedAxisNormBudget_pos n).le
      (projectedAxisDefectBudget_pos n) hnorm hprod'
  · exact normalizedOrthogonalChart_symm_norm_le W b (projectedAxisNormBudget_pos n).le hnorm
  · exact normalizedAxisBasis_covolume_ratio_bounds o b (projectedAxisDefectBudget_pos n)
      hnorm hprod' hpair

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

theorem exists_quantitative_projected_chart {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    let n := finrank ℝ Wᗮ
    let C : ℝ := 20 * ((n : ℝ) + 1) ^ 3
    ∃ b : Basis (Fin n) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∀ i, 0 < basisAxisScale b i) ∧
      (∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ Real.exp C * ‖x‖) ∧
      (∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ Real.exp C * ‖p‖) ∧
      Real.exp (-C) ≤
        ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) /
          (∏ i, (basisAxisScale b i : ℝ)) ∧
      ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) /
          (∏ i, (basisAxisScale b i : ℝ)) ≤ Real.exp C := by
  let n := finrank ℝ Wᗮ
  obtain ⟨b, hspan, hK, _, hf, hi, hvlo, hvhi⟩ := exists_normalized_projected_chart W
  refine ⟨b, hspan, hK, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (hf x).trans (mul_le_mul_of_nonneg_right (projectedChart_forwardBudget_le_exp n)
      (norm_nonneg x))
  · intro p
    exact (hi p).trans (mul_le_mul_of_nonneg_right (projectedChart_inverseBudget_le_exp n)
      (norm_nonneg p))
  · apply le_trans _ hvlo
    rw [Real.exp_neg, one_div]
    apply (inv_le_inv₀ (Real.exp_pos _) _).2
    · exact projectedChart_volumeBudget_le_exp n
    · have hB := projectedAxisNormBudget_pos n
      positivity
  · exact hvhi.trans (projectedChart_defectBudget_le_exp n)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.TopSubspaceAdaptedBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}

theorem exists_bounded_adapted_basis_with_top_subspace
    (F : NilpotentLieFiltration L s) (hs : 1 ≤ s) (e : Basis ι ℚ L)
    {η : Fin (s + 1) → Type*}
    (v : ∀ i, η i → F.layer (i.val + 1))
    (hspan : ∀ i, Submodule.span ℚ (Set.range (v i)) = ⊤)
    (K : Submodule ℚ L) (hK : K ≤ F.layer s) {κ : Type*} (vK : κ → K)
    (hspanK : Submodule.span ℚ (Set.range vK) = ⊤) {H : ℕ}
    (hv : ∀ i j k, RationalHeightLE (e.repr (v i j : L) k) H)
    (hvK : ∀ j k, RationalHeightLE (e.repr (vK j : L) k) H) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
      (S : Set (Fin (finrank ℚ L))),
      Monotone w ∧ IsCentralLieBasis b ∧
      (∀ j k, RationalHeightLE (e.repr (b j) k) H) ∧
      (∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) ∧
      K = Submodule.span ℚ (b '' S) := by
  classical
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  let bounded : Set L := {x | ∀ k, RationalHeightLE (e.repr x k) H}
  let flag : Fin (s + 1) → Submodule ℚ L := fun i => if i.val < s then F.layer (i.val + 1) else K
  have hflag : Antitone flag := by
    intro i j hij
    have hij' : i.val ≤ j.val := hij
    dsimp only [flag]
    split_ifs with hi hj
    · exact F.antitone (Nat.add_le_add_right hij 1)
    · omega
    · exact hK.trans (F.antitone (by omega))
    · exact le_rfl
  have hbounded (i : Fin (s + 1)) :
      Submodule.span ℚ (bounded ∩ (flag i : Set L)) = flag i := by
    dsimp only [flag]
    split_ifs with hi
    · exact span_inter_eq_of_spanning_family _ (v i) (hspan i) bounded (hv i)
    · exact span_inter_eq_of_spanning_family K vK hspanK bounded hvK
  have hzero : flag 0 = ⊤ := by
    simpa only [flag, Fin.val_zero, show 0 < s by omega, ite_true, Nat.zero_add] using F.one_eq_top
  have htotal : Submodule.span ℚ bounded = ⊤ := by
    apply top_unique
    rw [← hzero, ← hbounded 0]
    exact Submodule.span_mono Set.inter_subset_left
  obtain ⟨b, u, hu, hub, hbb, hbf⟩ :=
    exists_sorted_flag_basis_from_spanning_set flag hflag bounded htotal hbounded
  let w := fun i => min s (u i)
  have hw : Monotone w := fun i j hij => min_le_min le_rfl (hu hij)
  have hlayers (i : Fin (s + 1)) :
      F.layer (i.val + 1) = Submodule.span ℚ (b '' {j | i.val < w j}) := by
    by_cases hi : i.val < s
    · have h := hbf i
      simp only [flag, hi, ite_true] at h
      simpa only [w, lt_min_iff, hi, true_and] using h
    · have his : i.val = s := by omega
      rw [his, F.terminal]
      have hempty : {j | s < w j} = (∅ : Set (Fin (finrank ℚ L))) := by
        ext j
        simp [w]
      rw [hempty, Set.image_empty, Submodule.span_empty]
  have hlayer := F.layer_eq_span_of_weighted_flag b w (fun j =>
    (min_le_left s (u j)).trans (Nat.le_succ s)) hlayers
  refine ⟨b, w, {i | s < u i}, hw,
    centralLieBasis_of_sorted_filtration F b w hw hlayer, hbb, hlayer, ?_⟩
  simpa only [flag, lt_self_iff_false, ite_false] using hbf ⟨s, Nat.lt_succ_self s⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PatchKernelGridBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def gridPatchKernel (d N : ℕ) (hN : 8 ≤ N)
    (i : Fin d → Fin (N + 1)) : PatchKernel d where
  value x := regularizedTentPartition (uniformBoxGrid (1 / 4) N)
    (patchKernelGridRadius N) i (x + uniformBoxGrid (1 / 4) N i)
  nonneg x := (regularizedTentPartition_range _ (patchKernelGridRadius_pos (N := N) (by omega)) _ _).1
  le_one x := (regularizedTentPartition_range _ (patchKernelGridRadius_pos (N := N) (by omega)) _ _).2
  support x hx j := by
    have hnear : dist (x + uniformBoxGrid (1 / 4) N i) (uniformBoxGrid (1 / 4) N i) <
        2 * (patchKernelGridRadius N : ℝ) := by
      by_contra! hfar
      exact hx (regularizedTentPartition_zero _ _ _ _ hfar)
    have hj := dist_le_pi_dist (x + uniformBoxGrid (1 / 4) N i) (uniformBoxGrid (1 / 4) N i) j
    simp only [Real.dist_eq, Pi.add_apply, add_sub_cancel_right] at hj
    exact (hj.trans hnear.le).trans ((patchKernelGridRadius_small hN).trans (by norm_num))
  lip := (2 * ((N + 1) ^ d : ℕ) + 1) / patchKernelGridRadius N
  lipschitz := by
    have h := (regularizedTentPartition_lipschitz (uniformBoxGrid (ι := Fin d) (1 / 4) N)
      (patchKernelGridRadius_pos (N := N) (by omega)) i).comp
      (isometry_add_right (uniformBoxGrid (1 / 4) N i)).lipschitz
    simpa only [Fintype.card_fun, Fintype.card_fin, mul_one, Function.comp_def] using h

theorem gridPatchKernel_translate (d N : ℕ) (hN : 8 ≤ N)
    (i : Fin d → Fin (N + 1)) (x : Fin d → ℝ) :
    (gridPatchKernel d N hN i).value (x - uniformBoxGrid (1 / 4) N i) =
      regularizedTentPartition (uniformBoxGrid (1 / 4) N) (patchKernelGridRadius N) i x := by
  simp only [gridPatchKernel, sub_add_cancel]

theorem PatchKernel.grid_approx {d N : ℕ} (Φ : PatchKernel d) (hN : 8 ≤ N) (x : Fin d → ℝ) :
    |Φ.value x - ∑ i : Fin d → Fin (N + 1),
      Φ.value (uniformBoxGrid (1 / 4) N i) *
        regularizedTentPartition (uniformBoxGrid (1 / 4) N) (patchKernelGridRadius N) i x| ≤
      2 * Φ.lip * (patchKernelGridRadius N : ℝ) := by
  have hcover (y : Fin d → ℝ) (hy : Φ.value y ≠ 0) :=
    exists_uniformBoxGrid_approx (by norm_num : (0 : ℝ) < 1 / 4) (by omega : 0 < N) y (Φ.support y hy)
  have hr : (patchKernelGridRadius N : ℝ) = 2 * (1 / 4 : ℝ) / N := by
    simp only [patchKernelGridRadius, NNReal.coe_div, NNReal.coe_mul,
      NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_natCast]
    ring
  have h := regularizedTentPartition_approx (uniformBoxGrid (1 / 4) N)
    (show 0 < (patchKernelGridRadius N : ℝ) from patchKernelGridRadius_pos (N := N) (by omega))
    Φ.value Φ.lipschitz (fun y hy => by rw [hr]; exact hcover y hy) x
  simpa only [mul_comm] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace PolynomialPatch

variable {X : Type*} {s d N : ℕ}

noncomputable def gridKernelReplacement (A : PolynomialPatch X s d) (hN : 8 ≤ N)
    (i : Fin d → Fin (N + 1)) : PolynomialPatch X s d :=
  A.shiftedKernel (uniformBoxGrid (1 / 4) N i) (gridPatchKernel d N hN i)

theorem gridKernelReplacement_value (A : PolynomialPatch X s d) (hN : 8 ≤ N)
    (i : Fin d → Fin (N + 1)) (x : X → ℝ) :
    (A.gridKernelReplacement hN i).value x = ∑' z,
      regularizedTentPartition (uniformBoxGrid (1 / 4) N) (patchKernelGridRadius N) i
        ((A.form.slots x).residual z) := by
  simp only [gridKernelReplacement, shiftedKernel_value, gridPatchKernel_translate]

theorem gridKernelReplacement_approx (A : PolynomialPatch X s d) (hN : 8 ≤ N)
    (x : X → ℝ) :
    |A.value x - ∑ i : Fin d → Fin (N + 1),
      A.kernel.value (uniformBoxGrid (1 / 4) N i) * (A.gridKernelReplacement hN i).value x| ≤
      2 * A.kernel.lip * (patchKernelGridRadius N : ℝ) := by
  have h := (A.form.slots x).tsum_approx_finite_family A.kernel.value
    (regularizedTentPartition (uniformBoxGrid (1 / 4) N) (patchKernelGridRadius N))
    (fun i => A.kernel.value (uniformBoxGrid (1 / 4) N i))
    (R := 3 / 8) (by norm_num) (by positivity)
    (fun y hy j => (A.kernel.support y hy j).trans (by norm_num))
    (fun i y hy j => gridPatchKernel_original_support hN i y hy j)
    (A.kernel.grid_approx hN)
  simp_rw [gridKernelReplacement_value]
  exact h

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

def AllocatedShortIntegerAxis :=
  {a : Σ j : Fin m, Fin (n j) // basisAxisScale (b a.1) a.2 ≤ L ^ (a.1.val + 1)}

def allocatedShortIntegerSelection : AllocatedShortIntegerAxis U b L → Σ j, Fin (n j) :=
  Subtype.val

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CopiedLayerSpace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

noncomputable def copiedLayerPolynomial {I J K : Type*}
    (p : VectorPolynomial I ℝ (J → ℝ)) (q : VectorPolynomial I ℝ (K → ℝ)) :
    VectorPolynomial I ℝ (J ⊕ K → ℝ) := map copyLeft p + map copyRight q

theorem coefficients_copiedLayerPolynomial {I J K : Type*}
    (p : VectorPolynomial I ℝ (J → ℝ)) (q : VectorPolynomial I ℝ (K → ℝ)) (α : I →₀ ℕ) :
    coefficients (copiedLayerPolynomial p q) α = Sum.elim (coefficients p α) (coefficients q α) := by
  ext j
  cases j <;> simp [copiedLayerPolynomial, copyLeft, copyRight]

theorem copiedLayerPolynomial_mem {I J K : Type*}
    (W : Submodule ℝ (J → ℝ)) (V : Submodule ℝ (K → ℝ))
    (p : VectorPolynomial I ℝ (J → ℝ)) (q : VectorPolynomial I ℝ (K → ℝ))
    (hp : ∀ α, coefficients p α ∈ W) (hq : ∀ α, coefficients q α ∈ V) :
    ∀ α, coefficients (copiedLayerPolynomial p q) α ∈ copiedLayerSpace W V := by
  intro α
  rw [coefficients_copiedLayerPolynomial]
  exact ⟨hp α, hq α⟩

theorem copiedLayerPolynomial_degree {I J K : Type*}
    {p : VectorPolynomial I ℝ (J → ℝ)} {q : VectorPolynomial I ℝ (K → ℝ)}
    {w : I → ℕ} {h : ℕ} (hp : DegreeLE w h p) (hq : DegreeLE w h q) :
    DegreeLE w h (copiedLayerPolynomial p q) := by
  intro α hα
  rw [coefficients_copiedLayerPolynomial, hp α hα, hq α hα]
  ext j
  cases j <;> rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealChartReindexCoefficients
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem coefficients_substitute_reindex (e : τ ≃ σ)
    (P : VectorPolynomial σ R V) (α : τ →₀ ℕ) :
    coefficients (substitute (fun i => MvPolynomial.X (e.symm i)) P) α =
      coefficients P (α.mapDomain e) := by
  have hα : (α.mapDomain e).mapDomain e.symm = α := by
    ext i
    simp only [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  induction P using TensorProduct.induction_on with
  | zero => simp
  | tmul p v =>
    simp only [substitute_tmul, coefficients_tmul]
    change (MvPolynomial.aeval (MvPolynomial.X ∘ e.symm) p).coeff α • v = _
    rw [← MvPolynomial.rename_eq_aeval]
    exact congrArg (fun c : R => c • v)
      (by simpa only [hα] using
        MvPolynomial.coeff_rename_mapDomain e.symm e.symm.injective p (α.mapDomain e))
  | add p q hp hq => simp only [map_add, Finsupp.add_apply, hp, hq]

variable [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]

theorem coefficients_realChartSubstitute_reindex (e : τ ≃ σ)
    (P : VectorPolynomial σ ℚ V) (α : τ →₀ ℕ) :
    coefficients (realChartSubstitute (fun i => MvPolynomial.X (e.symm i)) P) α =
      coefficients P (α.mapDomain e) := by
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, coefficients_realCoefficientEquiv_symm,
    coefficients_substitute_reindex, coefficients_realCoefficientEquiv]

@[simp] theorem coefficients_zero_realChartSubstitute_reindex (e : τ ≃ σ)
    (P : VectorPolynomial σ ℚ V) :
    coefficients (realChartSubstitute (fun i => MvPolynomial.X (e.symm i)) P) 0 =
      coefficients P 0 := by
  simp only [coefficients_realChartSubstitute_reindex, Finsupp.mapDomain_zero]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.JointRationalSpaceDefiningMatrix
namespace OAI

section

namespace Erdos3

open scoped Matrix

namespace VectorPolynomial

theorem exists_jointRationalSpace_defining_matrix {J C V : Type*}
    [Fintype J] [Fintype C] [Fintype V]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) {H R : ℕ}
    (hH : 1 ≤ H)
    (hB : ∀ i j, RationalHeightLE (B i j) H)
    (hA : ∀ v j, RationalHeightLE (A v j) R) :
    ∃ Q : Matrix (J ⊕ V) J ℚ,
      (∀ v j, RationalHeightLE (Q v j)
        (max (imageDefiningHeight (Fintype.card C) (Fintype.card J) H) R)) ∧
      LinearMap.ker (Matrix.of (fun v j => (Q v j : ℝ))).mulVecLin =
        jointRationalSpace B A := by
  obtain ⟨Q, hQ, hQker⟩ := exists_real_span_defining_matrix B hH hB
  let A' : Matrix (J ⊕ V) J ℚ :=
    Matrix.of (fun v j => Sum.elim (fun i => Q i j) (fun v => A v j) v)
  refine ⟨A', ?_, ?_⟩
  · intro v j
    cases v with
    | inl i => exact (hQ i j).mono (le_max_left _ _)
    | inr v => exact (hA v j).mono (le_max_right _ _)
  · ext x
    change LinearMap.ker (Matrix.of (fun i j => (Q i j : ℝ))).mulVecLin =
      LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin at hQker
    change (Matrix.of (fun v j => (A' v j : ℝ)) *ᵥ x = 0) ↔
      x ∈ LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin ∧
      Matrix.of (fun v j => (A v j : ℝ)) *ᵥ x = 0
    rw [← hQker]
    change (Matrix.of (fun v j => (A' v j : ℝ)) *ᵥ x = 0) ↔
      (Matrix.of (fun i j => (Q i j : ℝ)) *ᵥ x = 0) ∧
      Matrix.of (fun v j => (A v j : ℝ)) *ᵥ x = 0
    constructor
    · intro hx
      exact ⟨funext (fun i => congrFun hx (.inl i)),
        funext (fun v => congrFun hx (.inr v))⟩
    · rintro ⟨hQx, hAx⟩
      ext v
      cases v with
      | inl i => exact congrFun hQx i
      | inr v => exact congrFun hAx v

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SubmoduleQuotientSectionBasis
namespace OAI

section

namespace Erdos3
open Module
open scoped Matrix TensorProduct

theorem exists_submoduleQuotientSectionBasis_with_coordinates
    {ι κ V : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (U : Submodule ℚ V) (D : Matrix κ ι ℚ) (T : Matrix ι κ ℚ)
    (hker : LinearMap.ker D.mulVecLin = U.map b.equivFun.toLinearMap)
    (hDT : D * T = 1) :
    ∃ (eQ : Basis κ ℚ (V ⧸ U)) (S : (V ⧸ U) →ₗ[ℚ] V),
      Function.RightInverse S U.mkQ ∧
      Function.RightInverse (S.baseChange ℝ) (U.mkQ.baseChange ℝ) ∧
      (∀ i j, b.repr (S (eQ j)) i = T i j) ∧
      (∀ i j, (b.baseChange ℝ).repr (S.baseChange ℝ ((eQ.baseChange ℝ) j)) i =
        (T i j : ℝ)) ∧
      ∀ j i, eQ.repr (U.mkQ (b i)) j = D j i := by
  have hsurj : Function.Surjective D.mulVec := by
    intro y
    refine ⟨T *ᵥ y, ?_⟩
    rw [Matrix.mulVec_mulVec, hDT, Matrix.one_mulVec]
  let eQ := submoduleQuotientCoordinateBasis b U D hker hsurj
  let S : (V ⧸ U) →ₗ[ℚ] V := b.equivFun.symm.toLinearMap.comp
    (T.mulVecLin.comp eQ.equivFun.toLinearMap)
  have hright : Function.RightInverse S U.mkQ := by
    intro y
    change U.mkQ (b.equivFun.symm (T *ᵥ eQ.equivFun y)) = y
    rw [← submoduleQuotientCoordinateEquiv_symm b U D hker hsurj T hDT]
    exact (submoduleQuotientCoordinateEquiv b U D hker hsurj).symm_apply_apply y
  have hentry (i : ι) (j : κ) : b.repr (S (eQ j)) i = T i j := by
    change b.equivFun (b.equivFun.symm (T *ᵥ eQ.equivFun (eQ j))) i = T i j
    rw [LinearEquiv.apply_symm_apply]
    simp [Matrix.mulVec, dotProduct, Basis.equivFun_self]
  refine ⟨eQ, S, hright, ?_, hentry, ?_, ?_⟩
  · have heq : U.mkQ.comp S = LinearMap.id := LinearMap.ext hright
    have heqR := congrArg (fun f : (V ⧸ U) →ₗ[ℚ] (V ⧸ U) => f.baseChange ℝ) heq
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at heqR
    intro x
    exact DFunLike.congr_fun heqR x
  · intro i j
    rw [scalarExtension_basis_coordinates, hentry]
  · intro j i
    have hmatrix := submoduleQuotientCoordinateBasis_matrix b U D hker hsurj
    have h := congrFun (congrFun hmatrix j) i
    simpa only [LinearMap.toMatrix_apply] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CylinderJointMass
namespace OAI

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

noncomputable def ProductCylinder.referenceMass (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (c : ProductCylinder X) : ℝ :=
  productFiberMass (FiniteProbabilityWeights.pi μ).weight c.1 (c.assignment base)

end Erdos3

end

end OAI
end


