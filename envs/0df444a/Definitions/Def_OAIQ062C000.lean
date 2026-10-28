-- Prove2me | Definitions.Def_OAIQ062C000
-- name    : OAIQ062C000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T23:53:42.567879+00:00
-- url     : https://prove2.me/theorems/1069cfef-8636-4d86-a06e-5374b0327d73
-- title:
--   Definitions bundle OAIQ062C000 of the split of OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 514 declarations of OpenAI's Lean: 116 definitions, 5 inductive types or structures and 393 theorems. The definitions and types are `OAI.Coulomb.Antisymmetric`, `OAI.Coulomb.AtomicBudgetHistory`, `OAI.Coulomb.AtomicBudgetHistory.center`, `OAI.Coulomb.ConfigSupported`, `OAI.Coulomb.Configuration`, `OAI.Coulomb.H1Vector`, `OAI.Coulomb.H1Vector.CoreSliceRegular`, `OAI.Coulomb.H1Vector.appendCut`, `OAI.Coulomb.H1Vector.coreSlice`, `OAI.Coulomb.H1Vector.labelCut`, `OAI.Coulomb.H1Vector.normalized`, `OAI.Coulomb.H1Vector.permutation`, `OAI.Coulomb.H1Vector.pullback`, `OAI.Coulomb.H1Vector.reindex`, `OAI.Coulomb.H1Vector.rsmul`, `OAI.Coulomb.H1Vector.scale`, `OAI.Coulomb.H1Vector.smoothMul`, `OAI.Coulomb.H1Vector.translate`, `OAI.Coulomb.H1Vector.zero`, `OAI.Coulomb.HardyCoordinates`, `OAI.Coulomb.Nuclei`, `OAI.Coulomb.PartlyAntisymmetric`, `OAI.Coulomb.PartlySupported`, `OAI.Coulomb.RecordedEnsemble`, `OAI.Coulomb.RecordedEnsemble.Conserves`, `OAI.Coulomb.RecordedEnsemble.CoreFermionic`, `OAI.Coulomb.RecordedEnsemble.OutSupported`, `OAI.Coulomb.RecordedEnsemble.rawSquare`, `OAI.Coulomb.RecordedEnsemble.totalForm`, `OAI.Coulomb.RecordedEnsemble.totalMass`, `OAI.Coulomb.Space`, `OAI.Coulomb.SpatiallySupported`, `OAI.Coulomb.SpinMode`, `OAI.Coulomb.Spins`, `OAI.Coulomb.allPositions`, `OAI.Coulomb.atomicCellScale`, `OAI.Coulomb.atomicIMS`, `OAI.Coulomb.atomicMeshCenter`, `OAI.Coulomb.atomicPatchMesh`, `OAI.Coulomb.atomicPatchRegion` and 81 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombRadii_FieldAnalysis_BinaryOrder`, `CoulombRadii_FieldAnalysis_BlockIndex`, `CoulombRadii_FieldAnalysis_CommonIsometryApply`, `CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv`, `CoulombRadii_FieldAnalysis_CoreCoulombPotential`, `CoulombRadii_FieldAnalysis_CorePerm`, `CoulombRadii_FieldAnalysis_CoreReindex`, `CoulombRadii_FieldAnalysis_CoulombBilinear`, `CoulombRadii_FieldAnalysis_FermionicCoefficients`, `CoulombRadii_FieldAnalysis_FlatDensityPower`, `CoulombRadii_FieldAnalysis_FrameDensity`, `CoulombRadii_FieldAnalysis_FrameOperator`, `CoulombRadii_FieldAnalysis_MeridianMap`, `CoulombRadii_FieldAnalysis_NearCoulombFiveHalves`, `CoulombRadii_FieldAnalysis_PermuteJoinBlock`, `CoulombRadii_FieldAnalysis_PhaseRegion`, `CoulombRadii_FieldAnalysis_PositiveField`, `CoulombRadii_FieldAnalysis_RawObservable`, `CoulombRadii_FieldAnalysis_RawThomasFermiEnergy`, `CoulombRadii_FieldAnalysis_RestrictedField`, `CoulombRadii_FieldAnalysis_SliceExpectation`, `CoulombRadii_FieldAnalysis_SortedObservable`, `CoulombRadii_FieldAnalysis_Space`, `CoulombRadii_FieldAnalysis_SpinMode`, `CoulombRadii_FieldAnalysis_UniformBall`, `CoulombRadii_FieldAnalysis_UnitNucleus`, `CoulombRadii_FieldAnalysis_WedgeMultiplicity`, `CoulombRadii_FormDomain_Add`, `CoulombRadii_FormDomain_AppendJensen`, `CoulombRadii_FormDomain_BallTrial`, `CoulombRadii_FormDomain_CoreKinetic`, `CoulombRadii_FormDomain_CoreSliceRegular`, `CoulombRadii_FormDomain_CubeGradient`, `CoulombRadii_FormDomain_HardyMollifier`, `CoulombRadii_FormDomain_HilbertBasisSumSqInner`, `CoulombRadii_FormDomain_L2MeasureInclusion`, `CoulombRadii_FormDomain_Pullback`, `CoulombRadii_FormDomain_RecordReindex`, `CoulombRadii_FormDomain_RegularizedHardyField`, `CoulombRadii_FormDomain_SchwartzSquareIntegrable`, `CoulombRadii_FormDomain_SmoothCompact`, `CoulombRadii_FormDomain_SortedCut`, `CoulombRadii_FormDomain_ThomasFermiKineticConstant`, `CoulombRadii_FormDomain_Translate`, `CoulombRadii_Localization_AtomicHistory`, `CoulombRadii_Localization_ConfigSupported`, `CoulombRadii_Localization_CutCombinatorics`, `CoulombRadii_Localization_CutCore`, `CoulombRadii_Localization_CutRefinement`, `CoulombRadii_Localization_DeletedLabels`, `CoulombRadii_Localization_Partial`, `CoulombRadii_Localization_RadialCut`, `CoulombRadii_Localization_TruncatedCoulomb`, `CoulombRadii_Packets_AtomicMesh`, `CoulombRadii_Packets_ComplexWindow`, `CoulombRadii_Packets_PacketDensity`, `CoulombRadii_Packets_PacketWindowed`, `CoulombRadii_Packets_ScaledWindow`, `CoulombRadii_Packets_WindowCoulomb`, `CoulombRadii_Propagation_NuclearPotential`, `CoulombRadii_Propagation_NuclearPotentialSplitJoin`, `CoulombRadii_RandomFields_ConditionalPositiveField`, `CoulombRadii_RandomFields_CutJensen`, `CoulombRadii_RandomFields_LocalizedEnsemble`, `CoulombRadii_RandomFields_RecordJensen`, `CoulombRadii_RandomFields_RecordedCount`, `CoulombRadii_RandomFields_RecordedEnsemble`, `CoulombRadii_Screening_AtomicBudgetHistory`, `CoulombRadii_Screening_CoreScreenedField`, `CoulombRadii_Screening_CountMoments`, `CoulombRadii_SpectralTheory_EigenspaceBasisSet`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ062C003`, `OAIQ062C004` and `OAIQ062C005`.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ062_CR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
/-- Mathlib's newer name for `aemeasurable_pi_lambda` (with `f` implicit). -/
theorem _root_.AEMeasurable.of_eval {δ ι : Type*} [Countable ι] {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {μ : MeasureTheory.Measure δ} {f : δ → ∀ i, π i}
    (h : ∀ i, AEMeasurable (fun a => f a i) μ) : AEMeasurable f μ := aemeasurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_BinaryOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped Classical
noncomputable section
namespace Coulomb

lemma exists_binary_order {n : ℕ} (p : Fin n → Fin 2) :
    ∃ m k : ℕ, ∃ e : Fin (m+k) ≃ Fin n,
      (∀ i : Fin m, p (e (Fin.castAdd k i))=0) ∧
      (∀ i : Fin k, p (e (Fin.natAdd m i))=1) := by
  let A := {i : Fin n // p i=0}
  let B := {i : Fin n // p i≠0}
  let m := Fintype.card A
  let k := Fintype.card B
  let eA : Fin m ≃ A := (Fintype.equivFin A).symm
  let eB : Fin k ≃ B := (Fintype.equivFin B).symm
  let e : Fin (m+k) ≃ Fin n := finSumFinEquiv.symm.trans ((eA.sumCongr eB).trans (Equiv.sumCompl (fun i => p i=0)))
  refine ⟨m,k,e,?_,?_⟩
  · intro i
    have he : e (Fin.castAdd k i) = (eA i).val := by
      simp only [e,Equiv.trans_apply,← finSumFinEquiv_apply_left,Equiv.symm_apply_apply,
        Equiv.sumCongr_apply,Sum.map_inl]
      rfl
    rw [he]
    exact (eA i).property
  · intro i
    have he : e (Fin.natAdd m i) = (eB i).val := by
      simp only [e,Equiv.trans_apply,← finSumFinEquiv_apply_right,Equiv.symm_apply_apply,
        Equiv.sumCongr_apply,Sum.map_inr]
      rfl
    rw [he]
    have h := (eB i).property
    exact Fin.eq_one_of_ne_zero _ h

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

namespace Coulomb

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Configuration (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin 3)
abbrev Spins (n : ℕ) := Fin n → Fin 2

structure Nuclei (M : ℕ) where
  nonempty : 0 < M
  position : Fin M → Space
  distinct : Function.Injective position
  charge : Fin M → ℝ
  charge_ge_one : ∀ j, 1 ≤ charge j

noncomputable def position {n : ℕ} (x : Configuration n) (i : Fin n) : Space :=
  WithLp.toLp 2 (fun b => x (i, b))

noncomputable def coulombKernel (x : Space) : ℝ := ‖x‖⁻¹

noncomputable def attraction {M : ℕ} (S : Nuclei M) (x : Space) : ℝ :=
  ∑ j, S.charge j * coulombKernel (x - S.position j)

noncomputable def permute {n : ℕ} (p : Equiv.Perm (Fin n))
    (x : Configuration n) : Configuration n :=
  WithLp.toLp 2 (fun ib => x (p ib.1, ib.2))

structure H1Vector (n : ℕ) where
  value : Spins n → Configuration n → ℂ
  gradient : Spins n → (Fin n × Fin 3) → Configuration n → ℂ
  value_L2 : ∀ s, MemLp (value s) 2 volume
  partial_L2 : ∀ s a, MemLp (gradient s a) 2 volume
  weak_partial : ∀ s a (φ : Configuration n → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, value s x * (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) =
        -(∫ x, gradient s a x * (φ x : ℂ))

def Antisymmetric {n : ℕ} (ψ : H1Vector n) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)) (s : Spins n),
    ∀ᵐ x ∂volume,
      ψ.value (s ∘ p) (permute p x) = ((p.sign : ℤ) : ℂ) * ψ.value s x

noncomputable def mass {n : ℕ} (ψ : H1Vector n) : ℝ :=
  ∑ s, ∫ x, ‖ψ.value s x‖ ^ 2

noncomputable def kinetic {n : ℕ} (ψ : H1Vector n) : ℝ :=
  (1 / 2 : ℝ) * ∑ s, ∑ a, ∫ x, ‖ψ.gradient s a x‖ ^ 2

noncomputable def nuclearEnergy {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) : ℝ :=
  ∑ s, ∫ x, (∑ i, attraction S (position x i)) * ‖ψ.value s x‖ ^ 2

noncomputable def pairEnergy {n : ℕ} (ψ : H1Vector n) : ℝ :=
  ∑ s, ∫ x, (∑ i : Fin n, ∑ j : Fin n,
    if i < j then coulombKernel (position x i - position x j) else 0) *
      ‖ψ.value s x‖ ^ 2

noncomputable def form {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) : ℝ :=
  kinetic ψ - nuclearEnergy S ψ + pairEnergy ψ

theorem memLp_two_real_mul {n : ℕ} {u : Configuration n → ℂ}
    (hu : MemLp u 2 volume) {f : Configuration n → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    MemLp (fun x => (f x : ℂ) * u x) 2 volume := by
  apply hu.of_le_mul (c := B) ((Complex.continuous_ofReal.comp hf).aestronglyMeasurable.mul
    hu.aestronglyMeasurable)
  filter_upwards [] with x
  simpa only [Pi.mul_apply, Function.comp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (hB x) (norm_nonneg (u x))

noncomputable def H1Vector.smoothMul {n : ℕ} (ψ : H1Vector n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B D : ℝ) (hB : ∀ x, |f x| ≤ B)
    (hD : ∀ a x, |fderiv ℝ f x (EuclideanSpace.single a 1)| ≤ D) : H1Vector n where
  value s x := (f x : ℂ) * ψ.value s x
  gradient s a x :=
    (fderiv ℝ f x (EuclideanSpace.single a 1) : ℂ) * ψ.value s x +
      (f x : ℂ) * ψ.gradient s a x
  value_L2 s := memLp_two_real_mul (ψ.value_L2 s) hf.continuous hB
  partial_L2 s a :=
    (memLp_two_real_mul (ψ.value_L2 s)
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const) (hD a)).add
      (memLp_two_real_mul (ψ.partial_L2 s a) hf.continuous hB)
  weak_partial s a φ hφ hφc := by
    let v := EuclideanSpace.single a (1 : ℝ)
    have hφL : MemLp (fun x => (φ x : ℂ)) 2 volume :=
      (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
        (hφc.comp_left (by simp))
    have hdφL : MemLp (fun x => (fderiv ℝ φ x v : ℂ)) 2 volume :=
      (Complex.continuous_ofReal.comp
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
        ((hφc.fderiv_apply ℝ v).comp_left (by simp))
    have hA : Integrable (fun x => ((f x : ℂ) * ψ.value s x) *
        (fderiv ℝ φ x v : ℂ)) volume :=
      (memLp_two_real_mul (ψ.value_L2 s) hf.continuous hB).integrable_mul hdφL
    have hB' : Integrable (fun x =>
        ((fderiv ℝ f x v : ℂ) * ψ.value s x) * (φ x : ℂ)) volume :=
      (memLp_two_real_mul (ψ.value_L2 s)
        ((hf.continuous_fderiv (by simp)).clm_apply continuous_const) (hD a)).integrable_mul hφL
    have hC : Integrable (fun x => ((f x : ℂ) * ψ.gradient s a x) *
        (φ x : ℂ)) volume :=
      (memLp_two_real_mul (ψ.partial_L2 s a) hf.continuous hB).integrable_mul hφL
    have hweak := ψ.weak_partial s a (f * φ) (hf.mul hφ) hφc.mul_left
    have hprod : ∀ x, ψ.value s x * (fderiv ℝ (f * φ) x v : ℂ) =
        ((f x : ℂ) * ψ.value s x) * (fderiv ℝ φ x v : ℂ) +
        ((fderiv ℝ f x v : ℂ) * ψ.value s x) * (φ x : ℂ) := by
      intro x
      rw [fderiv_mul (hf.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
      simp only [add_apply, smul_apply,
        smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]
      ring
    change (∫ x, ψ.value s x * (fderiv ℝ (f * φ) x v : ℂ)) = _ at hweak
    simp_rw [hprod] at hweak
    rw [integral_add hA hB'] at hweak
    have hr : ∀ x, ψ.gradient s a x * ((f * φ) x : ℂ) =
        ((f x : ℂ) * ψ.gradient s a x) * (φ x : ℂ) := by
      intro x
      simp only [Pi.mul_apply, Complex.ofReal_mul]
      ring
    simp_rw [hr] at hweak
    change (∫ x, ((f x : ℂ) * ψ.value s x) * (fderiv ℝ φ x v : ℂ)) = _
    simp_rw [add_mul]
    rw [integral_add hB' hC]
    linear_combination hweak

lemma norm_real_mul_sq (a : ℝ) (z : ℂ) :
    ‖(a : ℂ) * z‖ ^ 2 = a ^ 2 * ‖z‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

lemma norm_real_mul_add_sq (a b : ℝ) (u v : ℂ) :
    ‖(a : ℂ) * u + (b : ℂ) * v‖ ^ 2 =
      a ^ 2 * ‖u‖ ^ 2 + b ^ 2 * ‖v‖ ^ 2 +
        2 * a * b * (u.re * v.re + u.im * v.im) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem quadratic_partition_derivative {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Configuration n → ℝ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1) (x v : Configuration n) :
    ∑ i, f i x * fderiv ℝ (f i) x v = 0 := by
  classical
  have heq : (fun y => ∑ i, f i y ^ 2) = fun _ => (1 : ℝ) := funext hpart
  have hd := congrArg (fun g : Configuration n → ℝ => fderiv ℝ g x v) heq
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun i y => f i y ^ 2)
    (fun i _ => (hf i).differentiable (by simp) x |>.pow 2)] at hd
  simp only [sum_apply] at hd
  have hp : ∀ i, fderiv ℝ (fun y => f i y ^ 2) x v =
      2 * (f i x * fderiv ℝ (f i) x v) := by
    intro i
    change fderiv ℝ (f i ^ 2) x v = _
    rw [fderiv_pow 2 ((hf i).differentiable (by simp) x)]
    simp
    ring
  simp_rw [hp] at hd
  simp only [← Finset.mul_sum] at hd
  have hz : fderiv ℝ (fun _ : Configuration n => (1 : ℝ)) x v = 0 := by simp
  rw [hz] at hd
  linarith

theorem ims_pointwise {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Configuration n → ℝ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1) (x e : Configuration n) (u v : ℂ) :
    (∑ i, ‖(fderiv ℝ (f i) x e : ℂ) * u + (f i x : ℂ) * v‖ ^ 2) =
      ‖v‖ ^ 2 + (∑ i, (fderiv ℝ (f i) x e) ^ 2) * ‖u‖ ^ 2 := by
  classical
  simp_rw [norm_real_mul_add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, hpart, one_mul]
  have hcross : (∑ i, 2 * fderiv ℝ (f i) x e * f i x *
      (u.re * v.re + u.im * v.im)) = 0 := by
    conv_lhs => arg 2; intro i; rw [show
      2 * fderiv ℝ (f i) x e * f i x * (u.re * v.re + u.im * v.im) =
        (f i x * fderiv ℝ (f i) x e) *
          (2 * (u.re * v.re + u.im * v.im)) by ring]
    rw [← Finset.sum_mul, quadratic_partition_derivative f hf hpart, zero_mul]
  rw [hcross]
  ring

theorem kinetic_smooth_partition {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : H1Vector n) (f : ι → Configuration n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (B D : ℝ)
    (hB : ∀ i x, |f i x| ≤ B)
    (hD : ∀ i a x, |fderiv ℝ (f i) x (EuclideanSpace.single a 1)| ≤ D)
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1) :
    (∑ i, kinetic (ψ.smoothMul (f i) (hf i) B D (hB i) (hD i))) =
      kinetic ψ + (1 / 2 : ℝ) * ∑ s, ∑ a, ∫ x,
        (∑ i, (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2) *
          ‖ψ.value s x‖ ^ 2 := by
  classical
  let χ := fun i => ψ.smoothMul (f i) (hf i) B D (hB i) (hD i)
  have hblock : ∀ s a, (∑ i, ∫ x, ‖(χ i).gradient s a x‖ ^ 2) =
      (∫ x, ‖ψ.gradient s a x‖ ^ 2) +
      ∫ x, (∑ i, (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2) *
        ‖ψ.value s x‖ ^ 2 := by
    intro s a
    have hi : ∀ i, Integrable (fun x =>
        (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2 * ‖ψ.value s x‖ ^ 2)
        volume := by
      intro i
      have hL := memLp_two_real_mul (ψ.value_L2 s)
        (((hf i).continuous_fderiv (by simp)).clm_apply continuous_const) (hD i a)
      simpa only [norm_real_mul_sq] using hL.integrable_norm_pow (p := 2) (by decide)
    have herr : Integrable (fun x =>
        (∑ i, (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2) *
          ‖ψ.value s x‖ ^ 2) volume := by
      simp_rw [Finset.sum_mul]
      exact integrable_finsetSum _ (fun i _ => hi i)
    rw [← integral_finsetSum _ (fun i _ =>
      ((χ i).partial_L2 s a).integrable_norm_pow (p := 2) (by decide))]
    have heq : (fun x => ∑ i, ‖(χ i).gradient s a x‖ ^ 2) =
        fun x => ‖ψ.gradient s a x‖ ^ 2 +
          (∑ i, (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2) *
            ‖ψ.value s x‖ ^ 2 := by
      funext x
      exact ims_pointwise f hf hpart x (EuclideanSpace.single a 1)
        (ψ.value s x) (ψ.gradient s a x)
    rw [heq, integral_add ((ψ.partial_L2 s a).integrable_norm_pow (p := 2) (by decide)) herr]
  change (∑ i, kinetic (χ i)) = _
  unfold kinetic
  rw [← Finset.mul_sum]
  have hswap : (∑ i, ∑ s, ∑ a, ∫ x, ‖(χ i).gradient s a x‖ ^ 2) =
      ∑ s, ∑ a, ∑ i, ∫ x, ‖(χ i).gradient s a x‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_comm]
  rw [hswap]
  simp_rw [hblock, Finset.sum_add_distrib]
  ring

open ContinuousLinearMap
open scoped Convolution

structure HardyCoordinates (n : ℕ) (i : Fin n) where
  coord : Fin 3 → Configuration n → ℝ
  smooth : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (coord b)
  directional : ∀ a b x, fderiv ℝ (coord a) x (EuclideanSpace.single (i,b) 1) =
    if a = b then 1 else 0

noncomputable def blockRadiusSq {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) : ℝ := ∑ b : Fin 3, (R.coord b x)^2

lemma blockRadiusSq_nonneg {n : ℕ} (i : Fin n) (R : HardyCoordinates n i) (x : Configuration n) :
    0 ≤ blockRadiusSq i R x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma contDiff_blockRadiusSq {n : ℕ} (i : Fin n) (R : HardyCoordinates n i) :
    ContDiff ℝ (⊤ : ℕ∞) (blockRadiusSq i R) := by
  apply ContDiff.sum
  intro b _
  exact (R.smooth b).pow 2

lemma fderiv_blockRadiusSq {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) (b : Fin 3) :
    fderiv ℝ (blockRadiusSq i R) x (EuclideanSpace.single (i,b) 1) =
      2 * R.coord b x := by
  unfold blockRadiusSq
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun a (y : Configuration n) => (R.coord a y)^2)
    (fun a _ => ((R.smooth a).differentiable (by simp) x).pow 2)]
  simp only [sum_apply]
  have heach : ∀ a : Fin 3,
      fderiv ℝ (fun y : Configuration n => (R.coord a y)^2) x
        (EuclideanSpace.single (i,b) 1) =
          if a = b then 2 * R.coord b x else 0 := by
    intro a
    have hd := (((R.smooth a).differentiable (by simp) x).hasFDerivAt).pow 2
    rw [hd.fderiv]
    simp only [smul_apply, smul_eq_mul, R.directional]
    by_cases hab : a = b <;> simp [hab]
  simp_rw [heach]
  simp

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FermionicCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

noncomputable def permuteIsometry {n : ℕ} (p : Equiv.Perm (Fin n)) :
    Configuration n ≃ₗᵢ[ℝ] Configuration n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p.symm.prodCongr (Equiv.refl (Fin 3)))

lemma permuteIsometry_apply {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Configuration n) :
    permuteIsometry p x = permute p x := by
  ext a
  rfl

lemma permute_measurePreserving {n : ℕ} (p : Equiv.Perm (Fin n)) :
    MeasurePreserving (permute p) volume volume := by
  have e : permute p = ⇑(permuteIsometry p) := by
    funext x; exact (permuteIsometry_apply p x).symm
  rw [e]; exact (permuteIsometry p).measurePreserving

lemma position_permute {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Configuration n) (i : Fin n) :
    position (permute p x) i = position x (p i) := rfl

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

open scoped Classical

lemma inner_toLp_complex {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f g : A → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ x, star (f x) * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

lemma norm_toLp_sq_complex {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : A → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc
    (↑(‖hf.toLp f‖ ^ 2) : ℂ) = inner ℂ (hf.toLp f) (hf.toLp f) := by
      simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    _ = ∫ x, star (f x) * f x ∂μ := inner_toLp_complex hf hf
    _ = ∫ x, (↑(‖f x‖ ^ 2) : ℂ) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [mul_comm, Complex.ofReal_pow]
        exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (f x)

section FiberContraction
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]

lemma memLp_fiber_ae {f : B × A → ℂ} (hf : MemLp f 2 (ν.prod μ)) :
    ∀ᵐ b ∂ν, MemLp (fun a => f (b, a)) 2 μ := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hf.norm.integrable_sq.prod_right_ae]
    with b hb hbi
  exact (memLp_two_iff_integrable_sq_norm hb).2 hbi

omit [SigmaFinite μ] in
lemma integralInner_sq_le {f g : A → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ a, star (f a) * g a ∂μ‖ ^ 2 ≤
      (∫ a, ‖f a‖ ^ 2 ∂μ) * (∫ a, ‖g a‖ ^ 2 ∂μ) := by
  rw [← inner_toLp_complex hf hg, ← norm_toLp_sq_complex hf, ← norm_toLp_sq_complex hg,
    ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

noncomputable def fiberContract (v : A → ℂ) (f : B × A → ℂ) (b : B) : ℂ :=
  ∫ a, star (v a) * f (b, a) ∂μ

lemma fiberContract_memLp {v : A → ℂ} {f : B × A → ℂ}
    (hv : MemLp v 2 μ) (hf : MemLp f 2 (ν.prod μ)) :
    MemLp (fiberContract (μ := μ) v f) 2 ν := by
  have hm : AEStronglyMeasurable (fiberContract (μ := μ) v f) ν :=
    (hv.aestronglyMeasurable.star.comp_snd.mul hf.aestronglyMeasurable).integral_prod_right'
  apply (memLp_two_iff_integrable_sq_norm hm).2
  apply Integrable.mono' ((hf.norm.integrable_sq.integral_prod_left).const_mul
    (∫ a, ‖v a‖ ^ 2 ∂μ)) (hm.norm.pow 2)
  filter_upwards [memLp_fiber_ae hf] with b hb
  simpa only [fiberContract, Pi.pow_apply, Real.norm_eq_abs, abs_sq] using integralInner_sq_le hv hb

omit [SigmaFinite μ] [SigmaFinite ν] in

lemma tensorPair_memLp [SFinite μ] {w : B → ℂ} {v : A → ℂ}
    (hw : MemLp w 2 ν) (hv : MemLp v 2 μ) :
    MemLp (fun z : B × A => w z.1 * v z.2) 2 (ν.prod μ) := by
  apply (memLp_two_iff_integrable_sq_norm
    (hw.aestronglyMeasurable.comp_fst.mul hv.aestronglyMeasurable.comp_snd)).2
  simpa only [Pi.mul_apply, norm_mul, mul_pow] using hw.norm.integrable_sq.mul_prod hv.norm.integrable_sq

omit [SigmaFinite μ] [SigmaFinite ν] in
lemma integrable_star_mul {F : Type*} [MeasurableSpace F] {η : Measure F}
    {f g : F → ℂ} (hf : MemLp f 2 η) (hg : MemLp g 2 η) :
    Integrable (fun x => star (f x) * g x) η := by
  have h := L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)
  apply h.congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

lemma integral_tensorPair {w : B → ℂ} {v : A → ℂ} {f : B × A → ℂ}
    (hw : MemLp w 2 ν) (hv : MemLp v 2 μ) (hf : MemLp f 2 (ν.prod μ)) :
    (∫ z, star (w z.1 * v z.2) * f z ∂(ν.prod μ)) =
      ∫ b, star (w b) * fiberContract (μ := μ) v f b ∂ν := by
  rw [integral_prod _ (integrable_star_mul (tensorPair_memLp hw hv) hf)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun b => by
    dsimp only [fiberContract]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a => by
      simp only [star_mul]
      ring

end FiberContraction

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_ConfigSupported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
namespace Coulomb

def ConfigSupported {n : ℕ} (u : H1Vector n) (A : Set (Configuration n)) : Prop :=
  ∀ s, ∀ᵐ x ∂volume, x ∉ A → u.value s x = 0

lemma continuous_position {n : ℕ} (i : Fin n) :
    Continuous (fun x : Configuration n => position x i) := by
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi (fun b => (EuclideanSpace.proj (i,b)).continuous)

def allPositions {n : ℕ} (A : Set Space) : Set (Configuration n) :=
  {x | ∀ i, position x i ∈ A}

def SpatiallySupported {n : ℕ} (u : H1Vector n) (A : Set Space) : Prop :=
  ConfigSupported u (allPositions A)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_BlockIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
namespace Coulomb
noncomputable def blockIndex (m k : ℕ) :
    (Fin m × Fin 3) ⊕ (Fin k × Fin 3) ≃ Fin (m+k) × Fin 3 :=
  (Equiv.sumProdDistrib (Fin m) (Fin k) (Fin 3)).symm.trans
    (Equiv.prodCongr finSumFinEquiv (Equiv.refl _))

noncomputable def joinConfiguration (m k : ℕ) :
    (Configuration m × Configuration k) ≃L[ℝ] Configuration (m+k) :=
  EuclideanSpace.sumEquivProd.symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (blockIndex m k)).toContinuousLinearEquiv

lemma joinConfiguration_measurePreserving (m k : ℕ) :
    MeasurePreserving (joinConfiguration m k).toHomeomorph.toMeasurableEquiv
      (volume.prod volume) volume := by
  have h1 := WithLp.volume_preserving_toLp (Configuration m) (Configuration k)
  have h2 := (PiLp.sumPiLpEquivProdLpPiLp 2
    (fun _ : (Fin m × Fin 3) ⊕ (Fin k × Fin 3) => ℝ)).symm.measurePreserving
  have h3 := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (blockIndex m k)).measurePreserving
  exact h3.comp (h2.comp h1)

lemma joinConfiguration_left (m k : ℕ) (x : Configuration m) (y : Configuration k)
    (i : Fin m) (b : Fin 3) :
    joinConfiguration m k (x,y) (Fin.castAdd k i,b) = x (i,b) := by
  simp [joinConfiguration, blockIndex, EuclideanSpace.sumEquivProd,
    LinearIsometryEquiv.piLpCongrLeft_apply]

lemma joinConfiguration_right (m k : ℕ) (x : Configuration m) (y : Configuration k)
    (i : Fin k) (b : Fin 3) :
    joinConfiguration m k (x,y) (Fin.natAdd m i,b) = y (i,b) := by
  simp [joinConfiguration, blockIndex, EuclideanSpace.sumEquivProd,
    LinearIsometryEquiv.piLpCongrLeft_apply]

lemma joinConfiguration_right_single (m k : ℕ) (a : Fin k × Fin 3) :
    joinConfiguration m k (0, EuclideanSpace.single a 1) =
      EuclideanSpace.single (Fin.natAdd m a.1, a.2) 1 := by
  ext ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [joinConfiguration_left]
    simp only [PiLp.single_apply, PiLp.zero_apply, Prod.mk.injEq]
    split_ifs with h
    · have := congrArg (fun z : Fin (m+k) => z.val) h.1
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · rfl
  · intro j
    rw [joinConfiguration_right]
    simp [PiLp.single_apply, Prod.ext_iff]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_RegularizedHardyField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open ContinuousLinearMap
open scoped Convolution

noncomputable def regularizedHardyField {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (ε : ℝ) (b : Fin 3) (x : Configuration n) : ℝ :=
  R.coord b x / (blockRadiusSq i R x + ε)

lemma contDiff_regularizedHardyField {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (b : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedHardyField i R ε b) := by
  exact (R.smooth b).div ((contDiff_blockRadiusSq i R).add contDiff_const)
    (fun x => ne_of_gt (add_pos_of_nonneg_of_pos (blockRadiusSq_nonneg i R x) hε))

lemma fderiv_regularizedHardyField {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (b : Fin 3) (x : Configuration n) :
    fderiv ℝ (regularizedHardyField i R ε b) x (EuclideanSpace.single (i,b) 1) =
      (blockRadiusSq i R x + ε)⁻¹ -
        2 * (R.coord b x)^2 / (blockRadiusSq i R x + ε)^2 := by
  have hd := ((contDiff_blockRadiusSq i R).differentiable (by simp) x).hasFDerivAt.add_const ε
  have hne : blockRadiusSq i R x + ε ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (blockRadiusSq_nonneg i R x) hε)
  have hi := (hasFDerivAt_inv hne).comp x hd
  have hn := ((R.smooth b).differentiable (by simp) x).hasFDerivAt
  have hm := hn.fun_mul hi
  change fderiv ℝ (fun y : Configuration n =>
    R.coord b y * (blockRadiusSq i R y + ε)⁻¹) x _ = _
  simp only [Function.comp_apply] at hm
  rw [hm.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    ContinuousLinearMap.toSpanSingleton_apply]
  rw [fderiv_blockRadiusSq, R.directional]
  simp only [ite_true, mul_one]
  ring

lemma regularizedHardyField_sq_sum {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (ε : ℝ) (x : Configuration n) :
    (∑ b : Fin 3, (regularizedHardyField i R ε b x)^2) =
      blockRadiusSq i R x / (blockRadiusSq i R x + ε)^2 := by
  simp only [regularizedHardyField, div_pow, ← Finset.sum_div]
  rfl

lemma regularizedHardyField_divergence {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (x : Configuration n) :
    (∑ b : Fin 3, fderiv ℝ (regularizedHardyField i R ε b) x
      (EuclideanSpace.single (i,b) 1)) =
      (blockRadiusSq i R x + 3 * ε) / (blockRadiusSq i R x + ε)^2 := by
  simp_rw [fderiv_regularizedHardyField i R hε]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_div, ← Finset.mul_sum]
  change 3 * (blockRadiusSq i R x + ε)⁻¹ -
    2 * blockRadiusSq i R x / (blockRadiusSq i R x + ε)^2 = _
  have hne : blockRadiusSq i R x + ε ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (blockRadiusSq_nonneg i R x) hε)
  field_simp
  ring

lemma regularizedHardyField_weight {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (x : Configuration n) :
    (blockRadiusSq i R x + ε)⁻¹ ≤
      2 * (∑ b : Fin 3, fderiv ℝ (regularizedHardyField i R ε b) x
        (EuclideanSpace.single (i,b) 1)) -
      ∑ b : Fin 3, (regularizedHardyField i R ε b x)^2 := by
  rw [regularizedHardyField_divergence i R hε, regularizedHardyField_sq_sum]
  have hpos : 0 < blockRadiusSq i R x + ε :=
    add_pos_of_nonneg_of_pos (blockRadiusSq_nonneg i R x) hε
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hpos)).mp
  field_simp
  nlinarith

lemma integrable_smooth_mul_compact_deriv {n : ℕ} (u F : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u)
    (hF : Continuous F) (v : Configuration n) :
    Integrable (fun x => F x * fderiv ℝ u x v) := by
  exact (hF.mul ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport (huC.fderiv_apply ℝ v).mul_left

lemma integrable_smooth_deriv_mul_compact {n : ℕ} (u F : Configuration n → ℝ)
    (hu : Continuous u) (huC : HasCompactSupport u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Configuration n) :
    Integrable (fun x => fderiv ℝ F x v * u x) := by
  exact (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).mul hu).integrable_of_hasCompactSupport huC.mul_left

lemma integral_compact_ibp {n : ℕ} (u F : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Configuration n) :
    (∫ x, F x * fderiv ℝ u x v) = -(∫ x, fderiv ℝ F x v * u x) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_smooth_deriv_mul_compact u F hu.continuous huC hF v
  · exact integrable_smooth_mul_compact_deriv u F hu huC hF.continuous v
  · exact (hF.continuous.mul hu.continuous).integrable_of_hasCompactSupport huC.mul_left
  · intro x _; exact hF.differentiable (by simp) x
  · intro x _; exact hu.differentiable (by simp) x

lemma smooth_square_fderiv {n : ℕ} (u : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x v : Configuration n) :
    fderiv ℝ (fun y => (u y)^2) x v = 2 * u x * fderiv ℝ u x v := by
  rw [((hu.differentiable (by simp) x).hasFDerivAt.pow 2).fderiv]
  simp only [smul_apply, smul_eq_mul, Nat.reduceSub, pow_one, nsmul_eq_mul,
    Nat.cast_ofNat]

lemma integral_compact_ibp_deriv_form {n : ℕ} (u F : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Configuration n) :
    (∫ x, fderiv ℝ F x v * u x + F x * fderiv ℝ u x v) = 0 := by
  rw [integral_add
    (integrable_smooth_deriv_mul_compact u F hu.continuous huC hF v)
    (integrable_smooth_mul_compact_deriv u F hu huC hF.continuous v),
    integral_compact_ibp u F hu huC hF v]
  exact add_neg_cancel _

lemma integral_compact_ibp_square {n : ℕ} (u F : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Configuration n) :
    (∫ x, fderiv ℝ F x v * (u x)^2 + 2 * F x * u x * fderiv ℝ u x v) = 0 := by
  have hu2 : ContDiff ℝ (⊤ : ℕ∞) (fun x => (u x)^2) := hu.pow 2
  have hu2C : HasCompactSupport (fun x => (u x)^2) := huC.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have heq := integral_compact_ibp_deriv_form (fun x => (u x)^2) F hu2 hu2C hF v
  calc
    _ = (∫ x, fderiv ℝ F x v * (u x)^2 + F x * fderiv ℝ (fun y => (u y)^2) x v) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [smooth_square_fderiv u hu]
      ring
    _ = 0 := heq

lemma hardy_pointwise_algebra {ι : Type*} [Fintype ι]
    (u w : ℝ) (F D G : ι → ℝ)
    (hw : w ≤ 2 * ∑ b, D b - ∑ b, (F b)^2) :
    w * u^2 ≤ 4 * ∑ b, (G b)^2 +
      2 * ∑ b, (D b * u^2 + 2 * F b * u * G b) := by
  have hs : 0 ≤ ∑ b, (2 * G b + F b * u)^2 :=
    Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have hid : (∑ b, (2 * G b + F b * u)^2) =
      4 * ∑ b, (G b)^2 + 4 * u * ∑ b, F b * G b +
        u^2 * ∑ b, (F b)^2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hid2 : (∑ b, (D b * u^2 + 2 * F b * u * G b)) =
      u^2 * ∑ b, D b + 2 * u * ∑ b, F b * G b := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hp := mul_nonneg (sub_nonneg.mpr hw) (sq_nonneg u)
  rw [hid] at hs
  rw [hid2]
  nlinarith

lemma regularizedHardy_pointwise {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (u : Configuration n → ℝ) (x : Configuration n) :
    (blockRadiusSq i R x + ε)⁻¹ * (u x)^2 ≤
      4 * ∑ b : Fin 3, (fderiv ℝ u x (EuclideanSpace.single (i,b) 1))^2 +
      2 * ∑ b : Fin 3,
        (fderiv ℝ (regularizedHardyField i R ε b) x (EuclideanSpace.single (i,b) 1) *
          (u x)^2 + 2 * regularizedHardyField i R ε b x * u x *
          fderiv ℝ u x (EuclideanSpace.single (i,b) 1)) :=
  hardy_pointwise_algebra (u x) (blockRadiusSq i R x + ε)⁻¹
    (fun b => regularizedHardyField i R ε b x)
    (fun b => fderiv ℝ (regularizedHardyField i R ε b) x (EuclideanSpace.single (i,b) 1))
    (fun b => fderiv ℝ u x (EuclideanSpace.single (i,b) 1))
    (regularizedHardyField_weight i R hε x)

lemma integrable_compact_deriv_sq {n : ℕ} (u : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u) (v : Configuration n) :
    Integrable (fun x => (fderiv ℝ u x v)^2) := by
  have hc : Continuous (fun x => fderiv ℝ u x v) :=
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : HasCompactSupport (fun x => fderiv ℝ u x v) := huC.fderiv_apply ℝ v
  have hs2 : HasCompactSupport (fun x => (fderiv ℝ u x v)^2) :=
    hs.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  exact (hc.pow 2).integrable_of_hasCompactSupport hs2

lemma integrable_compact_ibp_square {n : ℕ} (u F : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Configuration n) :
    Integrable (fun x => fderiv ℝ F x v * (u x)^2 +
      2 * F x * u x * fderiv ℝ u x v) := by
  have hu2C : HasCompactSupport (fun x => (u x)^2) :=
    huC.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have h1 := integrable_smooth_deriv_mul_compact (fun x => (u x)^2)
    F (hu.pow 2).continuous hu2C hF v
  have h2 := integrable_smooth_mul_compact_deriv u (fun x => 2 * F x * u x)
    hu huC ((continuous_const.mul hF.continuous).mul hu.continuous) v
  exact h1.add h2

lemma integral_hardy_algebra {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (W : X → ℝ) (G D : ι → X → ℝ)
    (hW : Integrable W μ) (hG : ∀ b, Integrable (G b) μ)
    (hD : ∀ b, Integrable (D b) μ) (hD0 : ∀ b, (∫ x, D b x ∂μ) = 0)
    (hle : ∀ x, W x ≤ 4 * ∑ b, G b x + 2 * ∑ b, D b x) :
    (∫ x, W x ∂μ) ≤ 4 * ∑ b, ∫ x, G b x ∂μ := by
  have hGs : Integrable (fun x => ∑ b, G b x) μ :=
    integrable_finsetSum _ (fun b _ => hG b)
  have hDs : Integrable (fun x => ∑ b, D b x) μ :=
    integrable_finsetSum _ (fun b _ => hD b)
  have h := integral_mono hW ((hGs.const_mul 4).add (hDs.const_mul 2)) hle
  simp only [Pi.add_apply] at h
  rw [integral_add (hGs.const_mul 4) (hDs.const_mul 2),
    integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun b _ => hG b),
    integral_finsetSum _ (fun b _ => hD b)] at h
  simpa only [hD0, Finset.sum_const_zero, mul_zero, add_zero] using h

lemma integrable_compact_regularized_weight {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (u : Configuration n → ℝ)
    (hu : Continuous u) (huC : HasCompactSupport u) :
    Integrable (fun x => (blockRadiusSq i R x + ε)⁻¹ * (u x)^2) := by
  have hwcont : Continuous (fun x => (blockRadiusSq i R x + ε)⁻¹) :=
    ((contDiff_blockRadiusSq i R).continuous.add continuous_const).inv₀
      (fun x => ne_of_gt (add_pos_of_nonneg_of_pos (blockRadiusSq_nonneg i R x) hε))
  have hs : HasCompactSupport (fun x => (u x)^2) :=
    huC.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  exact (hwcont.mul (hu.pow 2)).integrable_of_hasCompactSupport hs.mul_left

lemma smooth_compact_regularized_hardy {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (u : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u) :
    (∫ x, (blockRadiusSq i R x + ε)⁻¹ * (u x)^2) ≤
      4 * ∑ b : Fin 3, ∫ x, (fderiv ℝ u x (EuclideanSpace.single (i,b) 1))^2 := by
  let G : Fin 3 → Configuration n → ℝ := fun b x =>
    (fderiv ℝ u x (EuclideanSpace.single (i,b) 1))^2
  let D : Fin 3 → Configuration n → ℝ := fun b x =>
    fderiv ℝ (regularizedHardyField i R ε b) x (EuclideanSpace.single (i,b) 1) *
      (u x)^2 + 2 * regularizedHardyField i R ε b x * u x *
      fderiv ℝ u x (EuclideanSpace.single (i,b) 1)
  have hG : ∀ b, Integrable (G b) := fun b => integrable_compact_deriv_sq u hu huC
    (EuclideanSpace.single (i,b) 1)
  have hD : ∀ b, Integrable (D b) := fun b => integrable_compact_ibp_square u
    (regularizedHardyField i R ε b) hu huC (contDiff_regularizedHardyField i R hε b)
    (EuclideanSpace.single (i,b) 1)
  have hD0 : ∀ b, (∫ x, D b x) = 0 := fun b => integral_compact_ibp_square u
    (regularizedHardyField i R ε b) hu huC (contDiff_regularizedHardyField i R hε b)
    (EuclideanSpace.single (i,b) 1)
  exact integral_hardy_algebra volume
    (fun x => (blockRadiusSq i R x + ε)⁻¹ * (u x)^2) G D
    (integrable_compact_regularized_weight i R hε u hu.continuous huC)
    hG hD hD0 (regularizedHardy_pointwise i R hε u)

lemma nonneg_fatou_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (F : ℕ → X → ℝ) (C : ℝ)
    (hF : ∀ n, Integrable (F n) μ) (hn : ∀ n x, 0 ≤ F n x)
    (hf : ∀ x, 0 ≤ f x)
    (ht : ∀ x, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x)))
    (hC : ∀ n, (∫ x, F n x ∂μ) ≤ C) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C := by
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hF n).aestronglyMeasurable)
      (Filter.Eventually.of_forall ht)
  have hb : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (F n x)) Filter.atTop ∂μ := by
        apply lintegral_congr
        intro x
        exact ((ENNReal.continuous_ofReal.tendsto _).comp (ht x)).liminf_eq.symm
      _ ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) Filter.atTop :=
        lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal C := by
        apply Filter.liminf_le_of_frequently_le (hu_le := Filter.isBoundedUnder_of ⟨0, fun _ => bot_le⟩)
        apply Filter.Eventually.frequently
        apply Filter.Eventually.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Filter.Eventually.of_forall (hn n))]
        exact ENNReal.ofReal_le_ofReal (hC n)
  have hfinite : Integrable f μ := ⟨hfm,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf)).2
      (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)⟩
  refine ⟨hfinite, ?_⟩
  have hCn : 0 ≤ C := (integral_nonneg (hn 0)).trans (hC 0)
  rw [← ofReal_integral_eq_lintegral_ofReal hfinite (Filter.Eventually.of_forall hf)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hCn).1 hb

lemma smooth_compact_hardy {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (u : Configuration n → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u) :
    Integrable (fun x => (blockRadiusSq i R x)⁻¹ * (u x)^2) ∧
    (∫ x, (blockRadiusSq i R x)⁻¹ * (u x)^2) ≤
      4 * ∑ b : Fin 3, ∫ x, (fderiv ℝ u x (EuclideanSpace.single (i,b) 1))^2 := by
  let eps : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have heps : ∀ k, 0 < eps k := fun k => one_div_pos.mpr (by positivity)
  let A := {x : Configuration n | blockRadiusSq i R x ≠ 0}
  have hA : MeasurableSet A :=
    ((contDiff_blockRadiusSq i R).continuous.measurable (measurableSet_singleton 0)).compl
  let F : ℕ → Configuration n → ℝ := fun k =>
    A.indicator (fun x => (blockRadiusSq i R x + eps k)⁻¹ * (u x)^2)
  have hF : ∀ k, Integrable (F k) := fun k =>
    (integrable_compact_regularized_weight i R (heps k) u hu.continuous huC).indicator hA
  have hFn : ∀ k x, 0 ≤ F k x := by
    intro k x
    exact Set.indicator_nonneg (fun x _ =>
      mul_nonneg (inv_nonneg.mpr (add_nonneg (blockRadiusSq_nonneg i R x) (heps k).le))
        (sq_nonneg (u x))) x
  have ht : ∀ x, Filter.Tendsto (fun k => F k x) Filter.atTop
      (nhds ((blockRadiusSq i R x)⁻¹ * (u x)^2)) := by
    intro x
    by_cases hx : x ∈ A
    · simp only [F, Set.indicator_of_mem hx]
      have ht0 : Filter.Tendsto eps Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have htt := (Filter.Tendsto.const_add (blockRadiusSq i R x) ht0).inv₀ (by simpa only [A, Set.mem_ofPred_eq, add_zero] using hx)
      simpa only [add_zero] using htt.mul_const ((u x)^2)
    · have hx0 : blockRadiusSq i R x = 0 := by simpa only [A, Set.mem_ofPred_eq, not_not] using hx
      simp only [F, Set.indicator_of_notMem hx, hx0, inv_zero, zero_mul]
      exact tendsto_const_nhds
  apply nonneg_fatou_integrable volume _ F _ hF hFn
    (fun x => mul_nonneg (inv_nonneg.mpr (blockRadiusSq_nonneg i R x)) (sq_nonneg (u x))) ht
  intro k
  calc
    (∫ x, F k x) ≤ ∫ x, (blockRadiusSq i R x + eps k)⁻¹ * (u x)^2 := by
      apply integral_mono (hF k)
        (integrable_compact_regularized_weight i R (heps k) u hu.continuous huC)
      intro x
      exact Set.indicator_le_self' (fun x _ =>
        mul_nonneg (inv_nonneg.mpr (add_nonneg (blockRadiusSq_nonneg i R x) (heps k).le))
          (sq_nonneg (u x))) x
    _ ≤ _ := smooth_compact_regularized_hardy i R (heps k) u hu huC

lemma convolution_sq_le {n : ℕ} (κ u : Configuration n → ℝ)
    (hκ : Continuous κ) (hκC : HasCompactSupport κ)
    (hκn : ∀ x, 0 ≤ κ x) (hκI : (∫ x, κ x) = 1)
    (hu : LocallyIntegrable u) (hu2 : Integrable (fun x => (u x)^2))
    (x : Configuration n) :
    ((κ ⋆ u) x)^2 ≤ (κ ⋆ (fun x => (u x)^2)) x := by
  have h1 : Integrable (fun y => κ (x-y) * u y) := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul, mul_comm] using
      hκC.convolutionExists_right (lsmul ℝ ℝ) hu hκ x
  have h2 : Integrable (fun y => κ (x-y) * (u y)^2) := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul, mul_comm] using
      hκC.convolutionExists_right (lsmul ℝ ℝ) hu2.locallyIntegrable hκ x
  have h0 : Integrable (fun y => κ (x-y)) :=
    (hκ.integrable_of_hasCompactSupport hκC).comp_sub_left x
  have heq : (∫ y, κ (x-y) * u y) = (κ ⋆ u) x := by
    rw [convolution_eq_swap]
    rfl
  have heq0 : (∫ y, κ (x-y)) = 1 := by
    rw [integral_sub_left_eq_self, hκI]
  have hm : (∫ y, (2 * (κ ⋆ u) x) * (κ (x-y) * u y) -
      ((κ ⋆ u) x)^2 * κ (x-y)) ≤ ∫ y, κ (x-y) * (u y)^2 := by
    apply integral_mono ((h1.const_mul _).sub (h0.const_mul _)) h2
    intro y
    simp only [Pi.sub_apply]
    nlinarith [mul_nonneg (hκn (x-y)) (sq_nonneg (u y - (κ ⋆ u) x))]
  rw [integral_sub (h1.const_mul _) (h0.const_mul _), integral_const_mul,
    integral_const_mul, heq, heq0] at hm
  have heq2 : (κ ⋆ (fun x => (u x)^2)) x = ∫ y, κ (x-y) * (u y)^2 := by
    rw [convolution_eq_swap]
    rfl
  rw [heq2]
  nlinarith

lemma convolution_sq_integral_le {n : ℕ} (κ u : Configuration n → ℝ)
    (hκ : Continuous κ) (hκC : HasCompactSupport κ)
    (hκn : ∀ x, 0 ≤ κ x) (hκI : (∫ x, κ x) = 1)
    (hu : LocallyIntegrable u) (hu2 : Integrable (fun x => (u x)^2)) :
    Integrable (fun x => ((κ ⋆ u) x)^2) ∧
    (∫ x, ((κ ⋆ u) x)^2) ≤ ∫ x, (u x)^2 := by
  have hdom : Integrable (κ ⋆ (fun x => (u x)^2)) :=
    (hκ.integrable_of_hasCompactSupport hκC).integrable_convolution (lsmul ℝ ℝ) hu2
  have hcont : Continuous (κ ⋆ u) :=
    hκC.continuous_convolution_left (lsmul ℝ ℝ) hκ hu
  have hsq : Integrable (fun x => ((κ ⋆ u) x)^2) := by
    apply hdom.mono' (hcont.pow 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact convolution_sq_le κ u hκ hκC hκn hκI hu hu2 x
  refine ⟨hsq, ?_⟩
  calc
    _ ≤ ∫ x, (κ ⋆ (fun x => (u x)^2)) x :=
      integral_mono hsq hdom (convolution_sq_le κ u hκ hκC hκn hκI hu hu2)
    _ = _ := by
      rw [integral_convolution (lsmul ℝ ℝ)
        (hκ.integrable_of_hasCompactSupport hκC) hu2, hκI]
      simp

lemma real_convolution_comm {n : ℕ} (u κ : Configuration n → ℝ) :
    u ⋆ κ = κ ⋆ u := by
  ext x
  rw [convolution_eq_swap, convolution_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => mul_comm _ _)

lemma fderiv_const_sub_comp {n : ℕ} (κ : Configuration n → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (x y v : Configuration n) :
    fderiv ℝ (fun z => κ (x - z)) y v = -(fderiv ℝ κ (x-y) v) := by
  have hd := ((hκ.differentiable (by simp) (x-y)).hasFDerivAt).comp y
    ((hasFDerivAt_id y).const_sub x)
  change HasFDerivAt (fun z => κ (x-z)) _ y at hd
  rw [hd.fderiv]
  simp

lemma weak_convolution_partial {n : ℕ} (u g κ : Configuration n → ℝ)
    (v : Configuration n) (hu : LocallyIntegrable u)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκC : HasCompactSupport κ)
    (hw : ∀ φ : Configuration n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x v) = -(∫ x, g x * φ x))
    (x : Configuration n) :
    fderiv ℝ (κ ⋆ u) x v = (κ ⋆ g) x := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun y => κ (x-y)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  have hφC : HasCompactSupport (fun y => κ (x-y)) :=
    hκC.comp_homeomorph (Homeomorph.subLeft x)
  have ht := hw (fun y => κ (x-y)) hφ hφC
  simp_rw [fderiv_const_sub_comp κ hκ x] at ht
  simp only [mul_neg, integral_neg, neg_inj] at ht
  rw [real_convolution_comm κ u,
    (hκC.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hu (hκ.of_le (by simp)) x).fderiv,
    convolution_precompR_apply (lsmul ℝ ℝ) hu (hκC.fderiv ℝ)
      (hκ.continuous_fderiv (by simp)) x v]
  rw [real_convolution_comm κ g]
  simpa only [convolution_def, lsmul_apply, smul_eq_mul] using ht

lemma ae_nonneg_fatou_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (F : ℕ → X → ℝ) (C : ℝ)
    (hF : ∀ n, Integrable (F n) μ) (hn : ∀ n x, 0 ≤ F n x)
    (hf : ∀ x, 0 ≤ f x)
    (ht : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x)))
    (hC : ∀ n, (∫ x, F n x ∂μ) ≤ C) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C := by
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hF n).aestronglyMeasurable)
      ht
  have hb : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (F n x)) Filter.atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ht] with x hx
        exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
      _ ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) Filter.atTop :=
        lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal C := by
        apply Filter.liminf_le_of_frequently_le (hu_le := Filter.isBoundedUnder_of ⟨0, fun _ => bot_le⟩)
        apply Filter.Eventually.frequently
        apply Filter.Eventually.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Filter.Eventually.of_forall (hn n))]
        exact ENNReal.ofReal_le_ofReal (hC n)
  have hfinite : Integrable f μ := ⟨hfm,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf)).2
      (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)⟩
  refine ⟨hfinite, ?_⟩
  have hCn : 0 ≤ C := (integral_nonneg (hn 0)).trans (hC 0)
  rw [← ofReal_integral_eq_lintegral_ofReal hfinite (Filter.Eventually.of_forall hf)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hCn).1 hb

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_HardyMollifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open ContinuousLinearMap
open scoped Convolution

noncomputable def hardyMollifier {n : ℕ} (k : ℕ) : ContDiffBump (0 : Configuration n) where
  rIn := 1 / ((k : ℝ) + 1)
  rOut := 2 / ((k : ℝ) + 1)
  rIn_pos := one_div_pos.mpr (by positivity)
  rIn_lt_rOut := div_lt_div_of_pos_right (by norm_num) (by positivity)

lemma hardyMollifier_tendsto {n : ℕ} :
    Filter.Tendsto (fun k => (hardyMollifier (n := n) k).rOut) Filter.atTop (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [hardyMollifier, mul_one_div, mul_zero] using h

lemma weak_compact_hardy {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (u : Configuration n → ℝ) (g : Fin 3 → Configuration n → ℝ)
    (hu : MemLp u 2) (hg : ∀ b, MemLp (g b) 2)
    (huC : HasCompactSupport u)
    (hw : ∀ b (φ : Configuration n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x (EuclideanSpace.single (i,b) 1)) =
        -(∫ x, g b x * φ x)) :
    Integrable (fun x => (blockRadiusSq i R x)⁻¹ * (u x)^2) ∧
    (∫ x, (blockRadiusSq i R x)⁻¹ * (u x)^2) ≤
      4 * ∑ b : Fin 3, ∫ x, (g b x)^2 := by
  let κ : ℕ → Configuration n → ℝ := fun k => (hardyMollifier k).normed volume
  have hκ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (κ k) := fun k =>
    (hardyMollifier k).contDiff_normed
  have hκC : ∀ k, HasCompactSupport (κ k) := fun k =>
    (hardyMollifier k).hasCompactSupport_normed
  have hκn : ∀ k x, 0 ≤ κ k x := fun k x => (hardyMollifier k).nonneg_normed x
  have hκI : ∀ k, (∫ x, κ k x) = 1 := fun k => (hardyMollifier k).integral_normed
  have hul : LocallyIntegrable u := hu.locallyIntegrable (by norm_num)
  have hus : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (κ k ⋆ u) := fun k =>
    (hκC k).contDiff_convolution_left (lsmul ℝ ℝ) (hκ k) hul
  have huc : ∀ k, HasCompactSupport (κ k ⋆ u) := fun k =>
    (hκC k).convolution (lsmul ℝ ℝ) huC
  have hh := fun k => smooth_compact_hardy i R (κ k ⋆ u) (hus k) (huc k)
  have ht : ∀ᵐ x ∂volume,
      Filter.Tendsto (fun k => (κ k ⋆ u) x) Filter.atTop (nhds (u x)) := by
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (φ := fun k => hardyMollifier k) (K := 2) hardyMollifier_tendsto _ hul
    apply Filter.Eventually.of_forall
    intro k
    simp only [hardyMollifier]
    simp only [mul_one_div, le_refl]
  apply ae_nonneg_fatou_integrable volume _
    (fun k x => (blockRadiusSq i R x)⁻¹ * ((κ k ⋆ u) x)^2) _
    (fun k => (hh k).1)
    (fun k x => mul_nonneg (inv_nonneg.mpr (blockRadiusSq_nonneg i R x)) (sq_nonneg _))
    (fun x => mul_nonneg (inv_nonneg.mpr (blockRadiusSq_nonneg i R x)) (sq_nonneg _))
  · filter_upwards [ht] with x hx
    exact (hx.pow 2).const_mul _
  · intro k
    apply (hh k).2.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro b _
    have heq : ∀ x, fderiv ℝ (κ k ⋆ u) x (EuclideanSpace.single (i,b) 1) =
        (κ k ⋆ g b) x := by
      intro x
      exact weak_convolution_partial u (g b) (κ k) _ hul (hκ k) (hκC k) (hw b) x
    simp_rw [heq]
    exact (convolution_sq_integral_le (κ k) (g b) (hκ k).continuous (hκC k)
      (hκn k) (hκI k) ((hg b).locallyIntegrable (by norm_num)) (hg b).integrable_sq).2

lemma ae_nonneg_fatou_integrable_of_bound_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (F : ℕ → X → ℝ) (C : ℝ) (B : ℕ → ℝ)
    (hF : ∀ n, Integrable (F n) μ) (hn : ∀ n x, 0 ≤ F n x)
    (hf : ∀ x, 0 ≤ f x)
    (ht : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x)))
    (hC : ∀ n, (∫ x, F n x ∂μ) ≤ B n)
    (hB : Filter.Tendsto B Filter.atTop (nhds C)) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C := by
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hF n).aestronglyMeasurable)
      ht
  have hb : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (F n x)) Filter.atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ht] with x hx
        exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
      _ ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) Filter.atTop :=
        lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ Filter.liminf (fun n => ENNReal.ofReal (B n)) Filter.atTop := by
        apply Filter.liminf_le_liminf (hu := Filter.isBoundedUnder_of ⟨0, fun _ => bot_le⟩)
          (hv := Filter.isCoboundedUnder_ge_of_le Filter.atTop (fun _ => le_top))
        apply Filter.Eventually.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Filter.Eventually.of_forall (hn n))]
        exact ENNReal.ofReal_le_ofReal (hC n)
      _ = ENNReal.ofReal C := ((ENNReal.continuous_ofReal.tendsto C).comp hB).liminf_eq
  have hfinite : Integrable f μ := ⟨hfm,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf)).2
      (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)⟩
  refine ⟨hfinite, ?_⟩
  have hCn : 0 ≤ C := ge_of_tendsto hB
    (Filter.Eventually.of_forall (fun n => (integral_nonneg (hn n)).trans (hC n)))
  rw [← ofReal_integral_eq_lintegral_ofReal hfinite (Filter.Eventually.of_forall hf)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hCn).1 hb

lemma realMemLp_bounded_mul {n : ℕ} (u f : Configuration n → ℝ)
    (hu : MemLp u 2) (hf : Continuous f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    MemLp (fun x => f x * u x) 2 := by
  apply hu.of_le_mul (c := B) (hf.aestronglyMeasurable.mul hu.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖f x * u x‖ ≤ B * ‖u x‖
  rw [norm_mul, Real.norm_eq_abs (f x)]
  exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

lemma weak_partial_bounded_mul {n : ℕ} (u g f : Configuration n → ℝ)
    (v : Configuration n) (hu : MemLp u 2) (hg : MemLp g 2)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {B D : ℝ} (hB : ∀ x, |f x| ≤ B) (hD : ∀ x, |fderiv ℝ f x v| ≤ D)
    (hw : ∀ φ : Configuration n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x v) = -(∫ x, g x * φ x))
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) :
    (∫ x, (f x * u x) * fderiv ℝ φ x v) =
      -(∫ x, (f x * g x + fderiv ℝ f x v * u x) * φ x) := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφL : MemLp φ 2 := hφ.continuous.memLp_of_hasCompactSupport hφC
  have hdφL : MemLp (fun x => fderiv ℝ φ x v) 2 :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hφC.fderiv_apply ℝ v)
  have hA : Integrable (fun x => (f x * u x) * fderiv ℝ φ x v) := (realMemLp_bounded_mul u f hu hf.continuous hB).integrable_mul hdφL
  have hB' : Integrable (fun x => (fderiv ℝ f x v * u x) * φ x) := (realMemLp_bounded_mul u _ hu hdf hD).integrable_mul hφL
  have hC : Integrable (fun x => (f x * g x) * φ x) := (realMemLp_bounded_mul g f hg hf.continuous hB).integrable_mul hφL
  have hweak := hw (f * φ) (hf.mul hφ) hφC.mul_left
  have hprod : ∀ x, u x * fderiv ℝ (f * φ) x v =
      (f x * u x) * fderiv ℝ φ x v + (fderiv ℝ f x v * u x) * φ x := by
    intro x
    rw [fderiv_mul (hf.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp_rw [hprod] at hweak
  rw [integral_add hA hB'] at hweak
  have hr : ∀ x, g x * (f * φ) x = (f x * g x) * φ x := by
    intro x
    simp only [Pi.mul_apply]
    ring
  simp_rw [hr] at hweak
  simp_rw [add_mul]
  rw [integral_add hC hB']
  linarith

lemma fderiv_smul_input {n : ℕ} (f : Configuration n → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (x v : Configuration n) :
    fderiv ℝ (fun z => f (c • z)) x v = c * fderiv ℝ f (c • x) v := by
  have hd := ((hf.differentiable (by simp) (c • x)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).const_smul c)
  change HasFDerivAt (fun z => f (c • z)) _ x at hd
  rw [hd.fderiv]
  simp

lemma exists_hardyCutoffs (n : ℕ) :
    ∃ (χ : ℕ → Configuration n → ℝ) (D : ℝ),
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (χ k)) ∧
      (∀ k, HasCompactSupport (χ k)) ∧
      (∀ k x, |χ k x| ≤ 1) ∧
      (∀ k a x, |fderiv ℝ (χ k) x (EuclideanSpace.single a 1)| ≤ D) ∧
      (∀ x, Filter.Tendsto (fun k => χ k x) Filter.atTop (nhds 1)) ∧
      (∀ a x, Filter.Tendsto (fun k => fderiv ℝ (χ k) x
        (EuclideanSpace.single a 1)) Filter.atTop (nhds 0)) := by
  let β : ContDiffBump (0 : Configuration n) := ⟨1, 2, by norm_num, by norm_num⟩
  let c : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hc : ∀ k, 0 < c k := fun k => one_div_pos.mpr (by positivity)
  have hc1 : ∀ k, c k ≤ 1 := by
    intro k
    simpa only [c, div_one] using
      one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num)
        (show (1 : ℝ) ≤ (k : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hct : Filter.Tendsto c Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hβ : ContDiff ℝ (⊤ : ℕ∞) (β : Configuration n → ℝ) := β.contDiff
  have hβC := β.hasCompactSupport
  have hβ1 : β 0 = 1 := β.one_of_mem_closedBall (by simp [β])
  obtain ⟨D, hD⟩ := ((hβC.fderiv ℝ).isCompact_range
    (hβ.continuous_fderiv (by simp))).exists_bound_of_continuousOn
      (f := fun z => z) continuous_id.continuousOn
  have hD' : ∀ x, ‖fderiv ℝ (β : Configuration n → ℝ) x‖ ≤ D :=
    fun x => hD _ ⟨x, rfl⟩
  have hDn : 0 ≤ D := (norm_nonneg _).trans (hD' 0)
  refine ⟨fun k x => β (c k • x), D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact hβ.comp (contDiff_id.const_smul (c k))
  · intro k
    exact hβC.comp_homeomorph (Homeomorph.smulOfNeZero (c k) (hc k).ne')
  · intro k x
    rw [abs_of_nonneg β.nonneg]
    exact β.le_one
  · intro k a x
    rw [fderiv_smul_input _ hβ, abs_mul, abs_of_pos (hc k)]
    have hnorm : |fderiv ℝ (β : Configuration n → ℝ) (c k • x)
        (EuclideanSpace.single a 1)| ≤ D := by
      calc
        _ = ‖fderiv ℝ (β : Configuration n → ℝ) (c k • x)
          (EuclideanSpace.single a 1)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ (β : Configuration n → ℝ) (c k • x)‖ *
          ‖EuclideanSpace.single (𝕜 := ℝ) a 1‖ := le_opNorm _ _
        _ ≤ D := by simpa using hD' (c k • x)
    exact (mul_le_mul_of_nonneg_left hnorm (hc k).le).trans
      (mul_le_of_le_one_left hDn (hc1 k))
  · intro x
    have ht : Filter.Tendsto (fun k => c k • x) Filter.atTop (nhds 0) := by
      simpa using hct.smul_const x
    simpa only [Function.comp_def, hβ1] using (hβ.continuous.tendsto 0).comp ht
  · intro a x
    have ht : Filter.Tendsto (fun k => c k • x) Filter.atTop (nhds 0) := by
      simpa using hct.smul_const x
    have hdf : Continuous (fun z => fderiv ℝ (β : Configuration n → ℝ) z
        (EuclideanSpace.single a 1)) :=
      (hβ.continuous_fderiv (by simp)).clm_apply continuous_const
    simp_rw [fderiv_smul_input _ hβ]
    simpa only [Function.comp_def, zero_mul] using hct.mul ((hdf.tendsto 0).comp ht)

lemma weak_hardy {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (u : Configuration n → ℝ) (g : Fin 3 → Configuration n → ℝ)
    (hu : MemLp u 2) (hg : ∀ b, MemLp (g b) 2)
    (hw : ∀ b (φ : Configuration n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x (EuclideanSpace.single (i,b) 1)) =
        -(∫ x, g b x * φ x)) :
    Integrable (fun x => (blockRadiusSq i R x)⁻¹ * (u x)^2) ∧
    (∫ x, (blockRadiusSq i R x)⁻¹ * (u x)^2) ≤
      4 * ∑ b : Fin 3, ∫ x, (g b x)^2 := by
  obtain ⟨χ, D, hχ, hχC, hχB, hχD, hχt, hχdt⟩ := exists_hardyCutoffs n
  let G : ℕ → Fin 3 → Configuration n → ℝ := fun k b x =>
    χ k x * g b x + fderiv ℝ (χ k) x (EuclideanSpace.single (i,b) 1) * u x
  have hdf : ∀ k b, Continuous (fun x => fderiv ℝ (χ k) x
      (EuclideanSpace.single (i,b) 1)) := fun k b =>
    ((hχ k).continuous_fderiv (by simp)).clm_apply continuous_const
  have hG : ∀ k b, MemLp (G k b) 2 := fun k b =>
    (realMemLp_bounded_mul (g b) (χ k) (hg b) (hχ k).continuous (hχB k)).add
      (realMemLp_bounded_mul u _ hu (hdf k b) (hχD k (i,b)))
  have hU : ∀ k, MemLp (fun x => χ k x * u x) 2 := fun k =>
    realMemLp_bounded_mul u (χ k) hu (hχ k).continuous (hχB k)
  have hUC : ∀ k, HasCompactSupport (fun x => χ k x * u x) := fun k =>
    (hχC k).mul_right
  have hW := fun k => weak_compact_hardy i R (fun x => χ k x * u x) (G k)
    (hU k) (hG k) (hUC k) (fun b φ hφ hφC =>
      weak_partial_bounded_mul u (g b) (χ k) _ hu (hg b) (hχ k) (hχB k)
        (hχD k (i,b)) (hw b) φ hφ hφC)
  have hGt : ∀ b x, Filter.Tendsto (fun k => G k b x) Filter.atTop (nhds (g b x)) := by
    intro b x
    have h := ((hχt x).mul_const (g b x)).add ((hχdt (i,b) x).mul_const (u x))
    simpa only [G, one_mul, zero_mul, add_zero] using h
  have hDnonneg : 0 ≤ D := (abs_nonneg _).trans (hχD 0 (i,0) 0)
  have hbound : ∀ k b x, |(G k b x)^2| ≤ 2 * (g b x)^2 + 2 * D^2 * (u x)^2 := by
    intro k b x
    rw [abs_of_nonneg (sq_nonneg _)]
    have hX : (χ k x)^2 ≤ 1 := by
      nlinarith [(sq_le_sq₀ (abs_nonneg (χ k x)) zero_le_one).mpr (hχB k x), sq_abs (χ k x)]
    have hY : (fderiv ℝ (χ k) x (EuclideanSpace.single (i,b) 1))^2 ≤ D^2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hDnonneg).mpr (hχD k (i,b) x)
    have hx := mul_le_mul_of_nonneg_right hX (sq_nonneg (g b x))
    have hy := mul_le_mul_of_nonneg_right hY (sq_nonneg (u x))
    dsimp only [G]
    nlinarith [sq_nonneg (χ k x * g b x -
      fderiv ℝ (χ k) x (EuclideanSpace.single (i,b) 1) * u x)]
  have hIt : ∀ b, Filter.Tendsto (fun k => ∫ x, (G k b x)^2) Filter.atTop
      (nhds (∫ x, (g b x)^2)) := by
    intro b
    apply tendsto_integral_of_dominated_convergence
      (fun x => 2 * (g b x)^2 + 2 * D^2 * (u x)^2)
    · intro k
      exact ((hG k b).aestronglyMeasurable.pow 2)
    · exact ((hg b).integrable_sq.const_mul 2).add (hu.integrable_sq.const_mul (2 * D^2))
    · intro k
      exact Filter.Eventually.of_forall (fun x => hbound k b x)
    · exact Filter.Eventually.of_forall (fun x => (hGt b x).pow 2)
  apply ae_nonneg_fatou_integrable_of_bound_tendsto volume _
    (fun k x => (blockRadiusSq i R x)⁻¹ * (χ k x * u x)^2) _
    (fun k => 4 * ∑ b : Fin 3, ∫ x, (G k b x)^2)
    (fun k => (hW k).1)
    (fun k x => mul_nonneg (inv_nonneg.mpr (blockRadiusSq_nonneg i R x)) (sq_nonneg _))
    (fun x => mul_nonneg (inv_nonneg.mpr (blockRadiusSq_nonneg i R x)) (sq_nonneg _))
  · apply Filter.Eventually.of_forall
    intro x
    have ht := (((hχt x).mul_const (u x)).pow 2).const_mul ((blockRadiusSq i R x)⁻¹)
    simpa only [one_mul] using ht
  · exact fun k => (hW k).2
  · exact (tendsto_finsetSum _ (fun b _ => hIt b)).const_mul 4

noncomputable def nuclearHardyCoordinates {n : ℕ} (i : Fin n) (R : Space) :
    HardyCoordinates n i where
  coord b x := x (i,b) - R b
  smooth b := (EuclideanSpace.proj (𝕜 := ℝ) (i,b)).contDiff.sub contDiff_const
  directional a b x := by
    have hd := ((EuclideanSpace.proj (𝕜 := ℝ) (i,a)).hasFDerivAt (x := x)).sub_const (R a)
    simp only [EuclideanSpace.coe_proj] at hd
    rw [hd.fderiv]
    by_cases hab : a = b
    · subst a; simp
    · simp [EuclideanSpace.proj, EuclideanSpace.single, hab]

noncomputable def pairHardyCoordinates {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    HardyCoordinates n i where
  coord b x := x (i,b) - x (j,b)
  smooth b := (EuclideanSpace.proj (𝕜 := ℝ) (i,b)).contDiff.sub
    (EuclideanSpace.proj (𝕜 := ℝ) (j,b)).contDiff
  directional a b x := by
    have hd := ((EuclideanSpace.proj (𝕜 := ℝ) (i,a)).hasFDerivAt (x := x)).sub
      ((EuclideanSpace.proj (𝕜 := ℝ) (j,a)).hasFDerivAt (x := x))
    simp only [EuclideanSpace.coe_proj] at hd
    change HasFDerivAt (fun x => x (i,a) - x (j,a)) _ x at hd
    rw [hd.fderiv]
    by_cases hab : a = b
    · subst a; simp [EuclideanSpace.proj, EuclideanSpace.single, hij.symm]
    · simp [EuclideanSpace.proj, EuclideanSpace.single, hab, hij.symm]

lemma realCLM_mul_ofReal (L : ℂ →L[ℝ] ℝ) (z : ℂ) (t : ℝ) :
    L (z * (t : ℂ)) = L z * t := by
  rw [mul_comm, mul_comm (L z)]
  exact L.map_smul t z

lemma weak_complex_component {n : ℕ} (u g : Configuration n → ℂ)
    (hu : MemLp u 2) (hg : MemLp g 2) (v : Configuration n)
    (hw : ∀ (φ : Configuration n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x v : ℂ)) = -(∫ x, g x * (φ x : ℂ)))
    (L : ℂ →L[ℝ] ℝ) (φ : Configuration n → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) :
    (∫ x, L (u x) * fderiv ℝ φ x v) = -(∫ x, L (g x) * φ x) := by
  have hφL : MemLp (fun x => (φ x : ℂ)) 2 :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hφC.comp_left (by simp))
  have hdφL : MemLp (fun x => (fderiv ℝ φ x v : ℂ)) 2 :=
    (Complex.continuous_ofReal.comp
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
      ((hφC.fderiv_apply ℝ v).comp_left (by simp))
  have hA := L.integral_comp_comm (hu.integrable_mul hdφL)
  have hB := L.integral_comp_comm (hg.integrable_mul hφL)
  simp only [Pi.mul_apply, realCLM_mul_ofReal] at hA hB
  rw [hA, hw φ hφ hφC, map_neg, ← hB]

lemma complex_norm_sq_components (z : ℂ) : ‖z‖^2 = z.re^2 + z.im^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

lemma complex_weak_hardy {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (u : Configuration n → ℂ) (g : Fin 3 → Configuration n → ℂ)
    (hu : MemLp u 2) (hg : ∀ b, MemLp (g b) 2)
    (hw : ∀ b (φ : Configuration n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x (EuclideanSpace.single (i,b) 1) : ℂ)) =
        -(∫ x, g b x * (φ x : ℂ))) :
    Integrable (fun x => (blockRadiusSq i R x)⁻¹ * ‖u x‖^2) ∧
    (∫ x, (blockRadiusSq i R x)⁻¹ * ‖u x‖^2) ≤
      4 * ∑ b : Fin 3, ∫ x, ‖g b x‖^2 := by
  have huR := Complex.reCLM.comp_memLp' hu
  have huI := Complex.imCLM.comp_memLp' hu
  have hgR := fun b => Complex.reCLM.comp_memLp' (hg b)
  have hgI := fun b => Complex.imCLM.comp_memLp' (hg b)
  have hr := weak_hardy i R (fun x => (u x).re) (fun b x => (g b x).re) huR hgR
    (fun b φ hφ hφC => weak_complex_component u (g b) hu (hg b) _ (hw b)
      Complex.reCLM φ hφ hφC)
  have hi := weak_hardy i R (fun x => (u x).im) (fun b x => (g b x).im) huI hgI
    (fun b φ hφ hφC => weak_complex_component u (g b) hu (hg b) _ (hw b)
      Complex.imCLM φ hφ hφC)
  have hsplit : ∀ x, (blockRadiusSq i R x)⁻¹ * ‖u x‖^2 =
      (blockRadiusSq i R x)⁻¹ * (u x).re^2 + (blockRadiusSq i R x)⁻¹ * (u x).im^2 :=
    fun x => by rw [complex_norm_sq_components, mul_add]
  constructor
  · have hsum : Integrable (fun x => (blockRadiusSq i R x)⁻¹ * (u x).re^2 +
        (blockRadiusSq i R x)⁻¹ * (u x).im^2) := hr.1.add hi.1
    exact hsum.congr (Filter.Eventually.of_forall (fun x => (hsplit x).symm))
  · simp_rw [hsplit]
    rw [integral_add hr.1 hi.1]
    have hb : ∀ b, (∫ x, ‖g b x‖^2) =
        (∫ x, (g b x).re^2) + (∫ x, (g b x).im^2) := by
      intro b
      simp_rw [complex_norm_sq_components]
      exact integral_add (hgR b).integrable_sq (hgI b).integrable_sq
    simp_rw [hb]
    rw [Finset.sum_add_distrib, mul_add]
    exact add_le_add hr.2 hi.2

lemma H1Vector.hardy {n : ℕ} (ψ : H1Vector n) (s : Spins n)
    (i : Fin n) (R : HardyCoordinates n i) :
    Integrable (fun x => (blockRadiusSq i R x)⁻¹ * ‖ψ.value s x‖^2) ∧
    (∫ x, (blockRadiusSq i R x)⁻¹ * ‖ψ.value s x‖^2) ≤
      4 * ∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2 :=
  complex_weak_hardy i R (ψ.value s) (fun b => ψ.gradient s (i,b))
    (ψ.value_L2 s) (fun b => ψ.partial_L2 s (i,b)) (fun b => ψ.weak_partial s (i,b))

noncomputable def hardyCoulomb {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) : ℝ := (Real.sqrt (blockRadiusSq i R x))⁻¹

lemma hardyCoulomb_nonneg {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) : 0 ≤ hardyCoulomb i R x := inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma hardyCoulomb_sq {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) : (hardyCoulomb i R x)^2 = (blockRadiusSq i R x)⁻¹ := by
  rw [hardyCoulomb, inv_pow, Real.sq_sqrt (blockRadiusSq_nonneg i R x)]

lemma measurable_hardyCoulomb {n : ℕ} (i : Fin n) (R : HardyCoordinates n i) :
    Measurable (hardyCoulomb i R) :=
  (contDiff_blockRadiusSq i R).continuous.measurable.sqrt.inv

lemma quadratic_young_reciprocal (t : ℝ) {η : ℝ} (hη : 0 < η) :
    t ≤ η * t^2 + 1 / (4 * η) := by
  calc
    t ≤ (4 * η^2 * t^2 + 1) / (4 * η) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * η)).mpr
      nlinarith [sq_nonneg (2 * η * t - 1)]
    _ = η * t^2 + 1 / (4 * η) := by field_simp

lemma H1Vector.coulomb_integrable_bound {n : ℕ} (ψ : H1Vector n) (s : Spins n)
    (i : Fin n) (R : HardyCoordinates n i) {η : ℝ} (hη : 0 < η) :
    Integrable (fun x => hardyCoulomb i R x * ‖ψ.value s x‖^2) ∧
    (∫ x, hardyCoulomb i R x * ‖ψ.value s x‖^2) ≤
      4 * η * (∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2) +
      (1 / (4 * η)) * (∫ x, ‖ψ.value s x‖^2) := by
  have hH := ψ.hardy s i R
  have hρ : Integrable (fun x => ‖ψ.value s x‖^2) :=
    (memLp_two_iff_integrable_sq_norm (ψ.value_L2 s).aestronglyMeasurable).mp (ψ.value_L2 s)
  have hB : Integrable (fun x => η * ((blockRadiusSq i R x)⁻¹ * ‖ψ.value s x‖^2) +
      (1 / (4 * η)) * ‖ψ.value s x‖^2) :=
    (hH.1.const_mul η).add (hρ.const_mul (1 / (4 * η)))
  have hpoint : ∀ x, hardyCoulomb i R x * ‖ψ.value s x‖^2 ≤
      η * ((blockRadiusSq i R x)⁻¹ * ‖ψ.value s x‖^2) +
      (1 / (4 * η)) * ‖ψ.value s x‖^2 := by
    intro x
    have ht := mul_le_mul_of_nonneg_right
      (quadratic_young_reciprocal (hardyCoulomb i R x) hη) (sq_nonneg ‖ψ.value s x‖)
    simpa only [hardyCoulomb_sq, add_mul, mul_assoc] using ht
  have hI : Integrable (fun x => hardyCoulomb i R x * ‖ψ.value s x‖^2) := by
    apply hB.mono' ((measurable_hardyCoulomb i R).aestronglyMeasurable.mul
      ((ψ.value_L2 s).aestronglyMeasurable.norm.pow 2))
    apply Filter.Eventually.of_forall
    intro x
    simpa only [Pi.mul_apply, Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (hardyCoulomb_nonneg i R x) (sq_nonneg _))] using hpoint x
  refine ⟨hI, ?_⟩
  have hm := integral_mono hI hB hpoint
  rw [integral_add (hH.1.const_mul η) (hρ.const_mul (1 / (4 * η))),
    integral_const_mul, integral_const_mul] at hm
  have hhard := mul_le_mul_of_nonneg_left hH.2 hη.le
  nlinarith

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SpinMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

abbrev SpinMode := Fin 2 × (Fin 3 → ℕ)

noncomputable def thomasFermiCoefficient : ℝ :=
  (3/10 : ℝ) * (3*Real.pi^2) ^ (2/3 : ℝ)

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_Translate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
lemma weak_partial_translate {n : ℕ} (ψ : H1Vector n) (c : Configuration n)
    (s : Spins n) (a : Fin n × Fin 3) (φ : Configuration n → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ x, ψ.value s (x+c) * (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) =
      -(∫ x, ψ.gradient s a (x+c) * (φ x : ℂ)) := by
  let Φ : Configuration n → ℝ := fun y => φ (y-c)
  have HΦ : ContDiff ℝ (⊤ : ℕ∞) Φ := hφ.comp (contDiff_id.sub contDiff_const)
  have HC : HasCompactSupport Φ := by
    simpa only [Φ, Function.comp_def, Homeomorph.coe_addRight, sub_eq_add_neg] using
      hcφ.comp_homeomorph (Homeomorph.addRight (-c))
  have Hd (y : Configuration n) : fderiv ℝ Φ y = fderiv ℝ φ (y-c) := by
    change fderiv ℝ (φ ∘ (fun y => id y - c)) y = _
    rw [fderiv_comp y (hφ.differentiable (by simp)).differentiableAt
      (differentiable_id.sub_const c).differentiableAt]
    simp only [fderiv_sub_const, id_eq, fderiv_fun_id, ContinuousLinearMap.comp_id]
  have H := ψ.weak_partial s a Φ HΦ HC
  simp_rw [Hd] at H
  have mp := measurePreserving_add_right (volume : Measure (Configuration n)) c
  rw [← (show MeasurePreserving (MeasurableEquiv.addRight c) volume volume from mp).integral_comp' (fun y => ψ.value s y *
    (fderiv ℝ φ (y-c) (EuclideanSpace.single a 1) : ℂ)),
    ← (show MeasurePreserving (MeasurableEquiv.addRight c) volume volume from mp).integral_comp' (fun y => ψ.gradient s a y * (Φ y : ℂ))] at H
  simpa only [Φ, MeasurableEquiv.coe_addRight, add_sub_cancel_right] using H

noncomputable def H1Vector.translate {n : ℕ} (ψ : H1Vector n) (c : Configuration n) :
    H1Vector n where
  value := fun s x => ψ.value s (x+c)
  gradient := fun s a x => ψ.gradient s a (x+c)
  value_L2 := fun s => (ψ.value_L2 s).comp_measurePreserving
    (measurePreserving_add_right volume c)
  partial_L2 := fun s a => (ψ.partial_L2 s a).comp_measurePreserving
    (measurePreserving_add_right volume c)
  weak_partial := weak_partial_translate ψ c

lemma permute_add {n : ℕ} (p : Equiv.Perm (Fin n)) (x c : Configuration n) :
    permute p (x+c) = permute p x + permute p c := by
  ext ij
  rfl

noncomputable def commonShift {n : ℕ} (t : Fin 3 → ℝ) : Configuration n :=
  WithLp.toLp 2 (fun ij => t ij.2)

lemma Antisymmetric.translate_common {n : ℕ} {ψ : H1Vector n} (hψ : Antisymmetric ψ)
    (t : Fin 3 → ℝ) : Antisymmetric (ψ.translate (commonShift t)) := by
  intro p s
  have H := (measurePreserving_add_right (volume : Measure (Configuration n))
    (commonShift t)).quasiMeasurePreserving.ae (hψ p s)
  filter_upwards [H] with x hx
  simpa only [H1Vector.translate, permute_add, show permute p (commonShift t) = commonShift t from rfl] using hx

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FlatDensityPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

noncomputable def commonIsometry {n : ℕ} (L : Space ≃ₗᵢ[ℝ] Space) :
    Configuration n ≃ₗᵢ[ℝ] Configuration n where
  toFun := fun x => WithLp.toLp 2 (fun ij => L (position x ij.1) ij.2)
  invFun := fun x => WithLp.toLp 2 (fun ij => L.symm (position x ij.1) ij.2)
  left_inv := by
    intro x
    ext ij
    change L.symm (L (position x ij.1)) ij.2 = x ij
    simp [position]
  right_inv := by
    intro x
    ext ij
    change L (L.symm (position x ij.1)) ij.2 = x ij
    simp [position]
  map_add' := by
    intro x y
    ext ij
    change L (position x ij.1 + position y ij.1) ij.2 = _
    rw [map_add]
    rfl
  map_smul' := by
    intro c x
    ext ij
    change L (c • position x ij.1) ij.2 = _
    rw [map_smul]
    rfl
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    change (∑ j, (L (position x i) j)^2) = ∑ j, (position x i j)^2
    rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq, L.norm_map]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
namespace Coulomb

lemma linear_form_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : EuclideanSpace ℝ ι →L[ℝ] ℝ) (v : EuclideanSpace ℝ ι) :
    T v = ∑ a, v a * T (EuclideanSpace.single a 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, smul_eq_mul]

lemma H1Vector.weak_directional {n : ℕ} (ψ : H1Vector n) (s : Spins n)
    (v : Configuration n) (φ : Configuration n → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ x, ψ.value s x * (fderiv ℝ φ x v : ℂ)) =
      -(∫ x, (∑ a, (v a : ℂ) * ψ.gradient s a x) * (φ x : ℂ)) := by
  have hφL : MemLp (fun x => (φ x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hcφ.comp_left (by simp))
  have hdφL (a : Fin n × Fin 3) :
      MemLp (fun x => (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
      ((hcφ.fderiv_apply ℝ _).comp_left (by simp))
  have Hd (x : Configuration n) := linear_form_eq_sum (fderiv ℝ φ x) v
  simp_rw [Hd, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
    Finset.sum_mul]
  have hA (a : Fin n × Fin 3) : Integrable (fun x => ψ.value s x *
      ((v a : ℂ) * (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ))) := by
    simpa only [Pi.mul_apply, mul_left_comm] using ((ψ.value_L2 s).integrable_mul (hdφL a)).const_mul (v a : ℂ)
  have hB (a : Fin n × Fin 3) : Integrable (fun x =>
      ((v a : ℂ) * ψ.gradient s a x) * (φ x : ℂ)) :=
    by simpa only [Pi.mul_apply, mul_assoc] using ((ψ.partial_L2 s a).integrable_mul hφL).const_mul (v a : ℂ)
  rw [integral_finsetSum _ (fun a _ => hA a), integral_finsetSum _ (fun a _ => hB a),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [mul_left_comm (ψ.value s _) (v a : ℂ), mul_assoc]
  rw [integral_const_mul, integral_const_mul, ψ.weak_partial s a φ hφ hcφ]
  ring

lemma H1Vector.weak_partial_isometry {n : ℕ} (ψ : H1Vector n)
    (L : Configuration n ≃ₗᵢ[ℝ] Configuration n) (s : Spins n) (a : Fin n × Fin 3)
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ x, ψ.value s (L x) * (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) =
      -(∫ x, (∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) * ψ.gradient s k (L x)) * (φ x : ℂ)) := by
  let Φ : Configuration n → ℝ := fun y => φ (L.symm y)
  have HΦ : ContDiff ℝ (⊤ : ℕ∞) Φ := hφ.comp L.symm.contDiff
  have HC : HasCompactSupport Φ := hcφ.comp_homeomorph L.symm.toHomeomorph
  have Hd (y : Configuration n) : fderiv ℝ Φ y (L (EuclideanSpace.single a 1)) =
      fderiv ℝ φ (L.symm y) (EuclideanSpace.single a 1) := by
    change fderiv ℝ (φ ∘ L.symm) y _ = _
    rw [fderiv_comp y (hφ.differentiable (by simp)).differentiableAt L.symm.differentiableAt]
    rw [show fderiv ℝ (⇑L.symm) y = L.symm.toContinuousLinearEquiv.toContinuousLinearMap from
      L.symm.toContinuousLinearEquiv.toContinuousLinearMap.fderiv]
    simp
  have H := ψ.weak_directional s (L (EuclideanSpace.single a 1)) Φ HΦ HC
  simp_rw [Hd] at H
  have mp : MeasurePreserving L.toHomeomorph.toMeasurableEquiv volume volume := L.measurePreserving
  rw [← mp.integral_comp' (fun y => ψ.value s y *
      (fderiv ℝ φ (L.symm y) (EuclideanSpace.single a 1) : ℂ)),
    ← mp.integral_comp' (fun y => (∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) *
      ψ.gradient s k y) * (Φ y : ℂ))] at H
  simpa [Φ] using H

noncomputable def H1Vector.pullback {n : ℕ} (ψ : H1Vector n)
    (L : Configuration n ≃ₗᵢ[ℝ] Configuration n) : H1Vector n where
  value := fun s x => ψ.value s (L x)
  gradient := fun s a x => ∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) * ψ.gradient s k (L x)
  value_L2 := fun s => (ψ.value_L2 s).comp_measurePreserving L.measurePreserving
  partial_L2 := fun s _a => memLp_finsetSum _ (fun k _ =>
    ((ψ.partial_L2 s k).comp_measurePreserving L.measurePreserving).const_mul _)
  weak_partial := ψ.weak_partial_isometry L

lemma isometry_complex_gradient_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (g : ι → ℂ) :
    (∑ a, ‖∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) * g k‖^2) = ∑ k, ‖g k‖^2 := by
  let u : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun k => (g k).re)
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun k => (g k).im)
  let b := (EuclideanSpace.basisFun ι ℝ).map L
  have hr (a : ι) : (∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) * g k).re =
      inner ℝ (b a) u := by
    simp [b, u, PiLp.inner_apply, Complex.mul_re, mul_comm]
  have hi (a : ι) : (∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) * g k).im =
      inner ℝ (b a) v := by
    simp [b, v, PiLp.inner_apply, Complex.mul_im, mul_comm]
  simp_rw [Complex.sq_norm, Complex.normSq_apply, ← pow_two, hr, hi]
  rw [Finset.sum_add_distrib, b.sum_sq_inner_right, b.sum_sq_inner_right,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [u, v, Finset.sum_add_distrib]

lemma mass_pullback {n : ℕ} (ψ : H1Vector n)
    (L : Configuration n ≃ₗᵢ[ℝ] Configuration n) : mass (ψ.pullback L) = mass ψ := by
  unfold mass H1Vector.pullback
  apply Finset.sum_congr rfl
  intro s _
  exact (show MeasurePreserving L.toHomeomorph.toMeasurableEquiv volume volume from
    L.measurePreserving).integral_comp' (fun x => ‖ψ.value s x‖^2)

lemma kinetic_pullback {n : ℕ} (ψ : H1Vector n)
    (L : Configuration n ≃ₗᵢ[ℝ] Configuration n) : kinetic (ψ.pullback L) = kinetic ψ := by
  unfold kinetic
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [← integral_finsetSum _ (fun a _ =>
    ((ψ.pullback L).partial_L2 s a).integrable_norm_pow (p := 2) (by decide)),
    ← integral_finsetSum _ (fun a _ =>
      (ψ.partial_L2 s a).integrable_norm_pow (p := 2) (by decide))]
  change (∫ x, ∑ a, ‖∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) * ψ.gradient s k (L x)‖^2) = _
  simp_rw [isometry_complex_gradient_sq]
  exact (show MeasurePreserving L.toHomeomorph.toMeasurableEquiv volume volume from
    L.measurePreserving).integral_comp' (fun x => ∑ a, ‖ψ.gradient s a x‖^2)

noncomputable section

def H1Vector.scale {n : ℕ} (c : ℂ) (u : H1Vector n) : H1Vector n where
  value := fun s x => c*u.value s x
  gradient := fun s a x => c*u.gradient s a x
  value_L2 := fun s => (u.value_L2 s).const_mul c
  partial_L2 := fun s a => (u.partial_L2 s a).const_mul c
  weak_partial := by
    intro s a φ hφ hC
    simp_rw [mul_assoc, integral_const_mul, u.weak_partial s a φ hφ hC]
    ring

def permutationIsometry {n : ℕ} (p : Equiv.Perm (Fin n)) :
    Configuration n ≃ₗᵢ[ℝ] Configuration n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.prodCongr p.symm (Equiv.refl _))

lemma permutationIsometry_apply {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Configuration n) :
    permutationIsometry p x = permute p x := by
  ext ⟨i,b⟩
  simp [permutationIsometry, permute, LinearIsometryEquiv.piLpCongrLeft_apply]

def H1Vector.permutation {n : ℕ} (u : H1Vector n) (p : Equiv.Perm (Fin n)) : H1Vector n where
  value := fun s => (u.pullback (permutationIsometry p)).value (s ∘ p)
  gradient := fun s => (u.pullback (permutationIsometry p)).gradient (s ∘ p)
  value_L2 := fun s => (u.pullback (permutationIsometry p)).value_L2 (s ∘ p)
  partial_L2 := fun s a => (u.pullback (permutationIsometry p)).partial_L2 (s ∘ p) a
  weak_partial := fun s a φ hφ hC =>
    (u.pullback (permutationIsometry p)).weak_partial (s ∘ p) a φ hφ hC

lemma permutation_value {n : ℕ} (u : H1Vector n) (p : Equiv.Perm (Fin n))
    (s : Spins n) (x : Configuration n) :
    (u.permutation p).value s x = u.value (s ∘ p) (permute p x) := by
  simp [H1Vector.permutation, H1Vector.pullback, permutationIsometry_apply]

def permutationSpins {n : ℕ} (p : Equiv.Perm (Fin n)) : Spins n ≃ Spins n :=
  Equiv.arrowCongr p.symm (Equiv.refl _)
end
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CommonIsometryApply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

lemma commonIsometry_permute {n : ℕ} (L : Space ≃ₗᵢ[ℝ] Space) (x : Configuration n)
    (p : Equiv.Perm (Fin n)) : commonIsometry L (permute p x) = permute p (commonIsometry L x) := by
  ext ij
  rfl

lemma Antisymmetric.pullback_common {n : ℕ} {ψ : H1Vector n} (hψ : Antisymmetric ψ)
    (L : Space ≃ₗᵢ[ℝ] Space) : Antisymmetric (ψ.pullback (commonIsometry L)) := by
  intro p s
  have H := (commonIsometry L).measurePreserving.quasiMeasurePreserving.ae (hψ p s)
  filter_upwards [H] with x hx
  change ψ.value (s ∘ p) (commonIsometry L (permute p x)) = _
  rw [commonIsometry_permute]
  exact hx

end Coulomb

open MeasureTheory Set
open scoped BigOperators Matrix

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_Add
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open ContinuousLinearMap
open scoped Convolution

lemma blockRadiusSq_nuclear {n : ℕ} (i : Fin n) (R : Space) (x : Configuration n) :
    blockRadiusSq i (nuclearHardyCoordinates i R) x = ‖position x i - R‖^2 := by
  simp [blockRadiusSq, nuclearHardyCoordinates, position, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs]

lemma blockRadiusSq_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : Configuration n) :
    blockRadiusSq i (pairHardyCoordinates i j hij) x = ‖position x i - position x j‖^2 := by
  simp [blockRadiusSq, pairHardyCoordinates, position, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs]

lemma hardyCoulomb_nuclear {n : ℕ} (i : Fin n) (R : Space) (x : Configuration n) :
    hardyCoulomb i (nuclearHardyCoordinates i R) x = coulombKernel (position x i - R) := by
  rw [hardyCoulomb, blockRadiusSq_nuclear, Real.sqrt_sq (norm_nonneg _)]
  rfl

lemma hardyCoulomb_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : Configuration n) :
    hardyCoulomb i (pairHardyCoordinates i j hij) x =
      coulombKernel (position x i - position x j) := by
  rw [hardyCoulomb, blockRadiusSq_pair, Real.sqrt_sq (norm_nonneg _)]
  rfl

lemma H1Vector.nuclear_coulomb_integrable_bound {n : ℕ} (ψ : H1Vector n)
    (s : Spins n) (i : Fin n) (R : Space) {η : ℝ} (hη : 0 < η) :
    Integrable (fun x => coulombKernel (position x i - R) * ‖ψ.value s x‖^2) ∧
    (∫ x, coulombKernel (position x i - R) * ‖ψ.value s x‖^2) ≤
      4 * η * (∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2) +
      (1 / (4 * η)) * (∫ x, ‖ψ.value s x‖^2) := by
  simpa only [hardyCoulomb_nuclear] using
    ψ.coulomb_integrable_bound s i (nuclearHardyCoordinates i R) hη

lemma H1Vector.pair_coulomb_integrable_bound {n : ℕ} (ψ : H1Vector n)
    (s : Spins n) (i j : Fin n) (hij : i ≠ j) {η : ℝ} (hη : 0 < η) :
    Integrable (fun x => coulombKernel (position x i - position x j) * ‖ψ.value s x‖^2) ∧
    (∫ x, coulombKernel (position x i - position x j) * ‖ψ.value s x‖^2) ≤
      4 * η * (∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2) +
      (1 / (4 * η)) * (∫ x, ‖ψ.value s x‖^2) := by
  simpa only [hardyCoulomb_pair] using
    ψ.coulomb_integrable_bound s i (pairHardyCoordinates i j hij) hη

lemma H1Vector.nuclear_integrable {M n : ℕ} (ψ : H1Vector n) (S : Nuclei M)
    (s : Spins n) :
    Integrable (fun x => (∑ i, attraction S (position x i)) * ‖ψ.value s x‖^2) := by
  simp only [attraction, Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have h := (ψ.nuclear_coulomb_integrable_bound s i (S.position j) (by norm_num : (0 : ℝ) < 1)).1
  simpa only [mul_assoc] using h.const_mul (S.charge j)

lemma H1Vector.pair_integrable {n : ℕ} (ψ : H1Vector n) (s : Spins n) :
    Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n,
      if i < j then coulombKernel (position x i - position x j) else 0) *
      ‖ψ.value s x‖^2) := by
  simp only [Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  by_cases hij : i < j
  · simp only [ite_eq_left hij]
    exact (ψ.pair_coulomb_integrable_bound s i j hij.ne (by norm_num : (0 : ℝ) < 1)).1
  · simp only [ite_eq_right hij, zero_mul]
    exact integrable_zero _ _ _

lemma potential_smooth_partition {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : H1Vector n) (f : ι → Configuration n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (B D : ℝ)
    (hB : ∀ i x, |f i x| ≤ B)
    (hD : ∀ i a x, |fderiv ℝ (f i) x (EuclideanSpace.single a 1)| ≤ D)
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1)
    (V : Configuration n → ℝ) (s : Spins n)
    (hI : ∀ i, Integrable (fun x => V x *
      ‖(ψ.smoothMul (f i) (hf i) B D (hB i) (hD i)).value s x‖^2)) :
    (∑ i, ∫ x, V x * ‖(ψ.smoothMul (f i) (hf i) B D (hB i) (hD i)).value s x‖^2) =
      ∫ x, V x * ‖ψ.value s x‖^2 := by
  rw [← integral_finsetSum _ (fun i _ => hI i)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change (∑ i, V x * ‖(f i x : ℂ) * ψ.value s x‖^2) = _
  simp_rw [norm_real_mul_sq]
  rw [← Finset.mul_sum, ← Finset.sum_mul, hpart, one_mul]

lemma nuclearEnergy_smooth_partition {M n : ℕ} {ι : Type*} [Fintype ι]
    (S : Nuclei M) (ψ : H1Vector n) (f : ι → Configuration n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (B D : ℝ)
    (hB : ∀ i x, |f i x| ≤ B)
    (hD : ∀ i a x, |fderiv ℝ (f i) x (EuclideanSpace.single a 1)| ≤ D)
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1) :
    (∑ i, nuclearEnergy S (ψ.smoothMul (f i) (hf i) B D (hB i) (hD i))) =
      nuclearEnergy S ψ := by
  unfold nuclearEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  exact potential_smooth_partition ψ f hf B D hB hD hpart _ s
    (fun i => (ψ.smoothMul (f i) (hf i) B D (hB i) (hD i)).nuclear_integrable S s)

lemma pairEnergy_smooth_partition {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : H1Vector n) (f : ι → Configuration n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (B D : ℝ)
    (hB : ∀ i x, |f i x| ≤ B)
    (hD : ∀ i a x, |fderiv ℝ (f i) x (EuclideanSpace.single a 1)| ≤ D)
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1) :
    (∑ i, pairEnergy (ψ.smoothMul (f i) (hf i) B D (hB i) (hD i))) = pairEnergy ψ := by
  unfold pairEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  exact potential_smooth_partition ψ f hf B D hB hD hpart _ s
    (fun i => (ψ.smoothMul (f i) (hf i) B D (hB i) (hD i)).pair_integrable s)

theorem form_smooth_partition {M n : ℕ} {ι : Type*} [Fintype ι]
    (S : Nuclei M) (ψ : H1Vector n) (f : ι → Configuration n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (B D : ℝ)
    (hB : ∀ i x, |f i x| ≤ B)
    (hD : ∀ i a x, |fderiv ℝ (f i) x (EuclideanSpace.single a 1)| ≤ D)
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1) :
    (∑ i, form S (ψ.smoothMul (f i) (hf i) B D (hB i) (hD i))) =
      form S ψ + (1 / 2 : ℝ) * ∑ s, ∑ a, ∫ x,
        (∑ i, (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2) *
          ‖ψ.value s x‖^2 := by
  simp only [form, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [kinetic_smooth_partition ψ f hf B D hB hD hpart,
    nuclearEnergy_smooth_partition S ψ f hf B D hB hD hpart,
    pairEnergy_smooth_partition ψ f hf B D hB hD hpart]
  ring

lemma mass_nonneg {n : ℕ} (ψ : H1Vector n) : 0 ≤ mass ψ :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

noncomputable def H1Vector.rsmul {n : ℕ} (t : ℝ) (ψ : H1Vector n) : H1Vector n where
  value s x := (t : ℂ) * ψ.value s x
  gradient s a x := (t : ℂ) * ψ.gradient s a x
  value_L2 s := memLp_two_real_mul (ψ.value_L2 s) continuous_const (fun _ => le_rfl)
  partial_L2 s a := memLp_two_real_mul (ψ.partial_L2 s a) continuous_const (fun _ => le_rfl)
  weak_partial s a f hf hc := by
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_const_mul, ψ.weak_partial s a f hf hc]
    ring

lemma Antisymmetric.rsmul {n : ℕ} {ψ : H1Vector n}
    (hψ : Antisymmetric ψ) (t : ℝ) : Antisymmetric (ψ.rsmul t) := by
  intro p s
  filter_upwards [hψ p s] with x hx
  change (t : ℂ) * ψ.value (s ∘ p) (permute p x) = _
  rw [hx]
  change _ = ((p.sign : ℤ) : ℂ) * ((t : ℂ) * ψ.value s x)
  ring

lemma mass_rsmul {n : ℕ} (ψ : H1Vector n) (t : ℝ) :
    mass (ψ.rsmul t) = t^2 * mass ψ := by
  unfold mass H1Vector.rsmul
  simp only [norm_real_mul_sq, integral_const_mul, Finset.mul_sum]

lemma kinetic_rsmul {n : ℕ} (ψ : H1Vector n) (t : ℝ) :
    kinetic (ψ.rsmul t) = t^2 * kinetic ψ := by
  unfold kinetic H1Vector.rsmul
  simp only [norm_real_mul_sq, integral_const_mul, ← Finset.mul_sum]
  ring

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_SmoothCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

noncomputable def positionCLM {n : ℕ} (i : Fin n) : Configuration n →L[ℝ] Space :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun b : Fin 3 =>
      (EuclideanSpace.proj (i,b) : Configuration n →L[ℝ] ℝ))

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_TruncatedCoulomb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma coulombKernel_nonneg (x : Space) : 0 ≤ coulombKernel x := inv_nonneg.mpr (norm_nonneg _)
lemma coulombKernel_measurable : Measurable coulombKernel := measurable_norm.inv
lemma coulombKernel_integrableOn_ball (R : ℝ) : IntegrableOn coulombKernel (Metric.ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by norm_num)
  · exact Filter.Eventually.of_forall (fun x => by simp [coulombKernel, Real.rpow_neg_one])
  · exact coulombKernel_measurable.aestronglyMeasurable

lemma coulombKernel_ball_integral {R : ℝ} (hR : 0 ≤ R) :
    (∫ x : Space in Metric.ball 0 R, coulombKernel x) = 2 * Real.pi * R^2 := by
  have H := integral_fun_norm_addHaar (volume : Measure Space)
    (fun t : ℝ => if t < R then t⁻¹ else 0)
  have hleft : (∫ x : Space in Metric.ball 0 R, coulombKernel x) =
      ∫ x : Space, (if ‖x‖ < R then ‖x‖⁻¹ else 0) := by
    rw [← integral_indicator measurableSet_ball]
    simp only [Set.indicator, Metric.mem_ball, dist_zero_right, coulombKernel]
  rw [hleft, H]
  have hball : volume.real (Metric.ball (0 : Space) 1) = 4 * Real.pi / 3 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
    norm_num
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  simp only [hdim, hball, nsmul_eq_mul, smul_eq_mul]
  have hint : (∫ t in Ioi (0:ℝ), t^(3-1) * (if t < R then t⁻¹ else 0)) = ∫ t in Ioo 0 R, t := by
    calc
      _ = ∫ t in Ioi (0:ℝ), (Iio R).indicator (fun u : ℝ => u) t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change 0 < t at ht
        by_cases h : t < R
        · simp only [h, ite_true, Set.indicator, mem_Iio]
          norm_num
          field_simp
        · simp [Set.indicator, h]
      _ = _ := by rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio, inter_comm, Ioi_inter_Iio]
  rw [hint, setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hR]
  norm_num [integral_id]
  ring

noncomputable def truncatedCoulomb (R : ℝ) (x : Space) : ℝ :=
  (Metric.ball (0:Space) R).indicator coulombKernel x
lemma truncatedCoulomb_integrable (R : ℝ) : Integrable (truncatedCoulomb R) :=
  (coulombKernel_integrableOn_ball R).integrable_indicator measurableSet_ball
lemma truncatedCoulomb_integral {R : ℝ} (hR : 0 ≤ R) :
    (∫ x, truncatedCoulomb R x) = 2*Real.pi*R^2 := by
  unfold truncatedCoulomb
  rw [integral_indicator measurableSet_ball, coulombKernel_ball_integral hR]

lemma coulomb_integrand_bound {f : Space → ℝ} {M R : ℝ} (hf0 : ∀ y, 0 ≤ f y)
    (hfM : ∀ y, f y ≤ M) (hR : 0 < R) (x y : Space) :
    coulombKernel (x-y) * f y ≤ M * truncatedCoulomb R (x-y) + R⁻¹ * f y := by
  by_cases h : x-y ∈ Metric.ball (0:Space) R
  · rw [truncatedCoulomb, Set.indicator_of_mem h]
    have H := mul_le_mul_of_nonneg_left (hfM y) (coulombKernel_nonneg (x-y))
    linarith [mul_nonneg (inv_nonneg.mpr hR.le) (hf0 y)]
  · rw [truncatedCoulomb, Set.indicator_of_notMem h, mul_zero, zero_add]
    have hn : R ≤ ‖x-y‖ := by simpa [Metric.mem_ball, dist_zero_right] using h
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hR hn) (hf0 y)

lemma coulomb_convolution_integrable {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {M R : ℝ} (hf0 : ∀ y, 0 ≤ f y) (hfM : ∀ y, f y ≤ M) (hR : 0 < R) (x : Space) :
    Integrable (fun y => coulombKernel (x-y) * f y) := by
  have hnear := (truncatedCoulomb_integrable R).comp_sub_left x
  apply ((hnear.const_mul M).add (hf.const_mul R⁻¹)).mono'
    (((coulombKernel_measurable.comp (measurable_const.sub measurable_id)).mul hm).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun y => by
    change ‖coulombKernel (x-y) * f y‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hf0 _))]
    exact coulomb_integrand_bound hf0 hfM hR x y)

lemma coulomb_convolution_bound {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {M R : ℝ} (hf0 : ∀ y, 0 ≤ f y) (hfM : ∀ y, f y ≤ M) (hR : 0 < R) (x : Space) :
    (∫ y, coulombKernel (x-y) * f y) ≤ 2*Real.pi*M*R^2 + R⁻¹ * ∫ y, f y := by
  have hnear := (truncatedCoulomb_integrable R).comp_sub_left x
  calc
    _ ≤ ∫ y, M * truncatedCoulomb R (x-y) + R⁻¹ * f y :=
      integral_mono (coulomb_convolution_integrable hf hm hf0 hfM hR x)
        ((hnear.const_mul M).add (hf.const_mul R⁻¹)) (coulomb_integrand_bound hf0 hfM hR x)
    _ = _ := by
      rw [integral_add (hnear.const_mul M) (hf.const_mul R⁻¹), integral_const_mul,
        integral_const_mul, integral_sub_left_eq_self, truncatedCoulomb_integral hR.le]
      ring

lemma coulomb_signed_convolution_integrable {f : Space → ℝ} (hf : Integrable f)
    (hm : Measurable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*f y) := by
  have h := coulomb_convolution_integrable hf.norm hm.norm (fun y => norm_nonneg _) hM
    (by norm_num : (0:ℝ) < 1) x
  apply h.mono' (((coulombKernel_measurable.comp (by fun_prop)).mul hm).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun y => by
    change ‖coulombKernel (x-y)*f y‖ ≤ coulombKernel (x-y)*‖f y‖
    rw [norm_mul, Real.norm_of_nonneg (coulombKernel_nonneg _)] )

lemma coulomb_pair_integrable {f g : Space → ℝ} (hf : Integrable f) (hfm : Measurable f)
    (hg : Integrable g) (hgm : Measurable g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) :
    Integrable (fun p : Space × Space => f p.1*g p.2*coulombKernel (p.1-p.2)) := by
  have hm : Measurable (fun p : Space × Space => f p.1*g p.2*coulombKernel (p.1-p.2)) :=
    ((hfm.comp measurable_fst).mul (hgm.comp measurable_snd)).mul (coulombKernel_measurable.comp (by fun_prop))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro x
    have hi := (coulomb_signed_convolution_integrable hg hgm hM x).const_mul (f x)
    apply hi.congr
    exact Filter.Eventually.of_forall (fun y => by dsimp only; ring)
  · let A : ℝ := 2*Real.pi*M + ∫ y, ‖g y‖
    have hb (x : Space) : (∫ y, coulombKernel (x-y)*‖g y‖) ≤ A := by
      simpa [A] using coulomb_convolution_bound hg.norm hgm.norm (fun y => norm_nonneg _) hM
        (by norm_num : (0:ℝ) < 1) x
    have he (x : Space) :
        (∫ y, ‖f x*g y*coulombKernel (x-y)‖) = ‖f x‖*(∫ y, coulombKernel (x-y)*‖g y‖) := by
      simp_rw [norm_mul, Real.norm_of_nonneg (coulombKernel_nonneg _)]
      simp_rw [mul_assoc, mul_comm ‖g _‖ (coulombKernel _)]
      rw [integral_const_mul]
    apply (hf.norm.mul_const A).mono' hm.aestronglyMeasurable.norm.integral_prod_right'
    exact Filter.Eventually.of_forall (fun x => by
      change ‖∫ y, ‖f x*g y*coulombKernel (x-y)‖‖ ≤ ‖f x‖*A
      rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _)), he]
      exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _))

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_CubeGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma positionCLM_single {n : ℕ} (i j : Fin n) (b : Fin 3) :
    positionCLM j (EuclideanSpace.single (i,b) 1) =
      if j = i then EuclideanSpace.single b 1 else 0 := by
  ext c
  by_cases h : j = i
  · subst j
    simp [positionCLM]
  · simp [positionCLM, h]

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PermuteJoinBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
namespace Coulomb
lemma position_join_right {m k : ℕ} (x : Configuration m) (y : Configuration k) (i : Fin k) :
    position (joinConfiguration m k (x,y)) (Fin.natAdd m i) = position y i := by
  ext b
  exact joinConfiguration_right m k x y i b

lemma position_split_right {m k : ℕ} (x : Configuration (m+k)) (i : Fin k) :
    position ((joinConfiguration m k).symm x).2 i = position x (Fin.natAdd m i) := by
  obtain ⟨⟨y,z⟩,rfl⟩ := (joinConfiguration m k).surjective x
  rw [ContinuousLinearEquiv.symm_apply_apply, position_join_right]

end Coulomb

open scoped BigOperators ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_WedgeMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
namespace Coulomb
lemma mass_permutation {n : ℕ} (u : H1Vector n) (p : Equiv.Perm (Fin n)) :
    mass (u.permutation p) = mass u := by
  calc
    _ = mass (u.pullback (permutationIsometry p)) := by
      unfold mass
      change (∑ s, ∫ x, ‖(u.pullback (permutationIsometry p)).value (permutationSpins p s) x‖^2) = _
      exact Equiv.sum_comp (permutationSpins p) (fun s => ∫ x, ‖(u.pullback (permutationIsometry p)).value s x‖^2)
    _ = _ := mass_pullback _ _
lemma kinetic_permutation {n : ℕ} (u : H1Vector n) (p : Equiv.Perm (Fin n)) :
    kinetic (u.permutation p) = kinetic u := by
  calc
    _ = kinetic (u.pullback (permutationIsometry p)) := by
      unfold kinetic
      congr 1
      change (∑ s, ∑ a, ∫ x, ‖(u.pullback (permutationIsometry p)).gradient (permutationSpins p s) a x‖^2) = _
      exact Equiv.sum_comp (permutationSpins p) (fun s => ∑ a, ∫ x, ‖(u.pullback (permutationIsometry p)).gradient s a x‖^2)
    _ = _ := kinetic_pullback _ _

lemma antisymmetric_scale {n : ℕ} (u : H1Vector n) (hu : Antisymmetric u) (c : ℂ) :
    Antisymmetric (u.scale c) := by
  intro p s
  filter_upwards [hu p s] with x hx
  change c*u.value (s ∘ p) (permute p x) = ((p.sign : ℤ) : ℂ)*(c*u.value s x)
  rw [hx]
  ring

def potentialEnergy {n : ℕ} (W : Configuration n → ℝ) (u : H1Vector n) : ℝ :=
  ∑ s, ∫ x, W x*‖u.value s x‖^2

lemma permute_integral_real {n : ℕ} (p : Equiv.Perm (Fin n)) (F : Configuration n → ℝ) :
    (∫ x, F (permute p x)) = ∫ x, F x := by
  exact (show MeasurePreserving (permutationIsometry p).toHomeomorph.toMeasurableEquiv
    volume volume from (permutationIsometry p).measurePreserving).integral_comp' F

lemma potentialEnergy_permutation {n : ℕ} (W : Configuration n → ℝ)
    (hW : ∀ p x, W (permute p x) = W x) (u : H1Vector n)
    (p : Equiv.Perm (Fin n)) : potentialEnergy W (u.permutation p) = potentialEnergy W u := by
  unfold potentialEnergy
  have H (s : Spins n) : (∫ x, W x*‖(u.permutation p).value s x‖^2) =
      ∫ x, W x*‖u.value (s ∘ p) x‖^2 := by
    simpa only [hW, permutation_value] using
      (permute_integral_real p (fun x => W x*‖u.value (s ∘ p) x‖^2))
  simp_rw [H]
  exact Equiv.sum_comp (permutationSpins p) (fun s => ∫ x, W x*‖u.value s x‖^2)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_NuclearPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical

namespace Coulomb
def nuclearPotential {M n : ℕ} (S : Nuclei M) (x : Configuration n) : ℝ :=
  ∑ i, attraction S (position x i)
def pairPotential {n : ℕ} (x : Configuration n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i < j then coulombKernel (position x i-position x j) else 0

lemma nuclearPotential_permute {M n : ℕ} (S : Nuclei M) (p : Equiv.Perm (Fin n))
    (x : Configuration n) : nuclearPotential S (permute p x) = nuclearPotential S x := by
  simp only [nuclearPotential, position_permute]
  exact Equiv.sum_comp p (fun i => attraction S (position x i))

lemma coulombKernel_sub_comm (x y : Space) : coulombKernel (x-y) = coulombKernel (y-x) := by
  simp only [coulombKernel, norm_sub_rev]

lemma twice_pairPotential {n : ℕ} (x : Configuration n) :
    2*pairPotential x = ∑ i : Fin n, ∑ j : Fin n, coulombKernel (position x i-position x j) := by
  have H (i j : Fin n) : coulombKernel (position x i-position x j) =
      (if i < j then coulombKernel (position x i-position x j) else 0)+
      (if j < i then coulombKernel (position x j-position x i) else 0) := by
    rcases lt_trichotomy i j with h|h|h
    · simp [h, not_lt_of_ge h.le]
    · subst j; simp [coulombKernel]
    · simp [h, not_lt_of_ge h.le, coulombKernel_sub_comm]
  have hs : pairPotential x = ∑ i : Fin n, ∑ j : Fin n,
      if j < i then coulombKernel (position x j-position x i) else 0 := by
    unfold pairPotential
    rw [Finset.sum_comm]
  calc
    2*pairPotential x = pairPotential x+pairPotential x := by ring
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ((if i < j then coulombKernel (position x i-position x j) else 0)+
         (if j < i then coulombKernel (position x j-position x i) else 0)) := by
      simp only [Finset.sum_add_distrib]
      change pairPotential x+pairPotential x = pairPotential x+_
      rw [hs]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact (H i j).symm

lemma pairPotential_permute {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Configuration n) :
    pairPotential (permute p x) = pairPotential x := by
  apply (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0))
  rw [twice_pairPotential, twice_pairPotential]
  simp_rw [position_permute]
  rw [Equiv.sum_comp p (fun i => ∑ j, coulombKernel (position x i-position x (p j)))]
  apply Finset.sum_congr rfl
  intro i _
  exact Equiv.sum_comp p (fun j => coulombKernel (position x i-position x j))

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_UnitNucleus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
namespace Coulomb
noncomputable def unitNucleus (R : Space) : Nuclei 1 where
  nonempty := by decide
  position := fun _ => R
  distinct := Function.injective_of_subsingleton _
  charge := fun _ => 1
  charge_ge_one := fun _ => le_rfl

lemma attraction_unitNucleus (R x : Space) :
    attraction (unitNucleus R) x = coulombKernel (x-R) := by
  simp [attraction, unitNucleus]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CoreCoulombPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
namespace Coulomb
lemma H1Vector.coulomb_density_prod_integrable {m : ℕ} (u : H1Vector m)
    (s : Spins m) (i : Fin m) (d : Space → ℝ) (hd : Integrable d) :
    Integrable (fun z : Configuration m × Space =>
      coulombKernel (position z.1 i-z.2)*‖u.value s z.1‖^2*d z.2)
      (volume.prod volume) := by
  let C := 4*(∑ b : Fin 3, ∫ x, ‖u.gradient s (i,b) x‖^2) +
      (1/4:ℝ)*(∫ x, ‖u.value s x‖^2)
  have hK : AEStronglyMeasurable (fun z : Configuration m × Space =>
      coulombKernel (position z.1 i-z.2)) (volume.prod volume) :=
    (((continuous_position i).measurable.comp measurable_fst).sub measurable_snd).norm.inv.aestronglyMeasurable
  have hF : AEStronglyMeasurable (fun z : Configuration m × Space =>
      coulombKernel (position z.1 i-z.2)*‖u.value s z.1‖^2*d z.2)
      (volume.prod volume) :=
    (hK.mul ((u.value_L2 s).aestronglyMeasurable.norm.pow 2).comp_fst).mul hd.1.comp_snd
  have hN (y : Space) :
      (∫ x, ‖coulombKernel (position x i-y)*‖u.value s x‖^2*d y‖) =
      (∫ x, coulombKernel (position x i-y)*‖u.value s x‖^2)*‖d y‖ := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with x
    have hk : 0 ≤ coulombKernel (position x i-y) := inv_nonneg.mpr (norm_nonneg _)
    rw [norm_mul,Real.norm_of_nonneg (mul_nonneg hk (sq_nonneg _))]
  apply (integrable_prod_iff' hF).2
  constructor
  · filter_upwards [] with y
    exact ((u.nuclear_coulomb_integrable_bound s i y (by norm_num : (0:ℝ)<1)).1).mul_const (d y)
  · apply (hd.norm.const_mul C).mono' hF.prod_swap.norm.integral_prod_right'
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    change (∫ x, ‖coulombKernel (position x i-y)*‖u.value s x‖^2*d y‖) ≤ C*‖d y‖
    rw [hN]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [C,mul_one,one_div] using
      (u.nuclear_coulomb_integrable_bound s i y (by norm_num : (0:ℝ)<1)).2

noncomputable def coreCoulombPotential {m : ℕ} (u : H1Vector m) (z : Space) : ℝ :=
  ∑ s : Spins m, ∑ i : Fin m, ∫ x, coulombKernel (position x i-z)*‖u.value s x‖^2

lemma coreCoulombPotential_nonneg {m : ℕ} (u : H1Vector m) (z : Space) :
    0 ≤ coreCoulombPotential u z := by
  apply Finset.sum_nonneg
  intro s _
  apply Finset.sum_nonneg
  intro i _
  exact integral_nonneg (fun x => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (sq_nonneg _))

lemma coreCoulombPotential_mul_integrable {m : ℕ} (u : H1Vector m)
    (d : Space → ℝ) (hd : Integrable d) :
    Integrable (fun z => coreCoulombPotential u z*d z) := by
  simp only [coreCoulombPotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro s _
  apply integrable_finsetSum
  intro i _
  have H := (u.coulomb_density_prod_integrable s i d hd).integral_prod_right
  simpa only [integral_mul_const] using H

lemma coreCoulombPotential_fubini {m : ℕ} (u : H1Vector m)
    (d : Space → ℝ) (hd : Integrable d) :
    (∫ z, coreCoulombPotential u z*d z) =
      ∑ s : Spins m, ∑ i : Fin m,
        ∫ x, (∫ z, coulombKernel (position x i-z)*d z)*‖u.value s x‖^2 := by
  have hI (s : Spins m) (i : Fin m) : Integrable
      (fun z => (∫ x, coulombKernel (position x i-z)*‖u.value s x‖^2)*d z) := by
    have H := (u.coulomb_density_prod_integrable s i d hd).integral_prod_right
    simpa only [integral_mul_const] using H
  simp only [coreCoulombPotential,Finset.sum_mul]
  rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ => hI s i))]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_finsetSum _ (fun i _ => hI s i)]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [← integral_mul_const]
  rw [← integral_prod_symm _ (u.coulomb_density_prod_integrable s i d hd),
    integral_prod _ (u.coulomb_density_prod_integrable s i d hd)]
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with z
  ring

end Coulomb

open scoped Classical
namespace Coulomb

lemma attraction_nonneg {M : ℕ} (S : Nuclei M) (x : Space) : 0 ≤ attraction S x := by
  exact Finset.sum_nonneg (fun j _ => mul_nonneg ((by norm_num : (0:ℝ)≤1).trans (S.charge_ge_one j))
    (coulombKernel_nonneg _))

end Coulomb

open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_CoreSliceRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal

open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

lemma ae_all_zero_of_continuous {X T : Type*} [MeasurableSpace X]
    {μ : Measure X} [TopologicalSpace T] [TopologicalSpace.SeparableSpace T]
    (A : X → T → ℂ) (hc : ∀ x, Continuous (A x))
    (hz : ∀ t, ∀ᵐ x ∂μ, A x t = 0) : ∀ᵐ x ∂μ, ∀ t, A x t = 0 := by
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense T
  have hDz : ∀ᵐ x ∂μ, ∀ t ∈ D, A x t = 0 := (ae_ball_iff hD).mpr (fun t _ => hz t)
  filter_upwards [hDz] with x hx
  have he : A x = fun _ => 0 := Continuous.ext_on hdense (hc x) continuous_const hx
  intro t
  exact congrFun he t

section SmoothSlices
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)] in
lemma compact_tensor_test {χ : E → ℝ} {φ : F → ℝ}
    (hχ : HasCompactSupport χ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun z : E × F => χ z.1 * φ z.2) := by
  apply HasCompactSupport.of_support_subset_isCompact (hχ.prod hφ)
  intro z hz
  simp only [Function.mem_support, mul_ne_zero_iff] at hz
  exact ⟨subset_tsupport _ hz.1, subset_tsupport _ hz.2⟩

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)] in
lemma tensor_test_deriv {χ : E → ℝ} {φ : F → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (v : F) (z : E × F) :
    fderiv ℝ (fun z : E × F => χ z.1 * φ z.2) z (0, v) =
      χ z.1 * fderiv ℝ φ z.2 v := by
  have h1 := (hχ.differentiable (by simp) z.1).hasFDerivAt.comp z (hasFDerivAt_fst (𝕜 := ℝ))
  have h2 := (hφ.differentiable (by simp) z.2).hasFDerivAt.comp z (hasFDerivAt_snd (𝕜 := ℝ))
  change (fderiv ℝ ((χ ∘ Prod.fst) * (φ ∘ Prod.snd)) z) (0,v) = _
  rw [(h1.mul h2).fderiv]
  simp

omit [SigmaFinite (volume : Measure E)] in
lemma test_complex_memLp {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) :
    MemLp (fun x => (φ x : ℂ)) 2 volume :=
  (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
    (hφC.comp_left (by simp))

omit [SigmaFinite (volume : Measure E)] in
lemma test_direction_complex_memLp {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) (v : E) :
    MemLp (fun x => (fderiv ℝ φ x v : ℂ)) 2 volume :=
  (Complex.continuous_ofReal.comp
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
      ((hφC.fderiv_apply ℝ v).comp_left (by simp))

lemma weak_slice_fixed_test {u g : E × F → ℂ}
    (hu : MemLp u 2 (volume.prod volume)) (hg : MemLp g 2 (volume.prod volume))
    (v : F)
    (hw : ∀ (η : E × F → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ z, u z * (fderiv ℝ η z (0,v) : ℂ) ∂(volume.prod volume)) =
        -(∫ z, g z * (η z : ℂ) ∂(volume.prod volume)))
    (φ : F → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) :
    ∀ᵐ x ∂(volume : Measure E),
      (∫ y, u (x,y) * (fderiv ℝ φ y v : ℂ)) = -(∫ y, g (x,y) * (φ y : ℂ)) := by
  let dφ : F → ℂ := fun y => (fderiv ℝ φ y v : ℂ)
  let cφ : F → ℂ := fun y => (φ y : ℂ)
  have hd := test_direction_complex_memLp hφ hφC v
  have hc := test_complex_memLp hφ hφC
  let A := fiberContract (μ := volume) dφ u
  let B := fiberContract (μ := volume) cφ g
  have hA : MemLp A 2 volume := fiberContract_memLp hd hu
  have hB : MemLp B 2 volume := fiberContract_memLp hc hg
  have hzero : ∀ᵐ x ∂(volume : Measure E), (A + B) x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero ((hA.add hB).locallyIntegrable (by norm_num))
    intro χ hχ hχC
    have hχL := test_complex_memLp hχ hχC
    have H := hw (fun z => χ z.1 * φ z.2)
      ((hχ.comp contDiff_fst).mul (hφ.comp contDiff_snd)) (compact_tensor_test hχC hφC)
    simp_rw [tensor_test_deriv hχ hφ v, Complex.ofReal_mul] at H
    have H1 := integral_tensorPair hχL hd hu
    have H2 := integral_tensorPair hχL hc hg
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal] at H1 H2
    have L1 : (∫ z, u z * ((χ z.1 : ℂ) * (fderiv ℝ φ z.2 v : ℂ)) ∂(volume.prod volume)) =
      ∫ x, (χ x : ℂ) * A x := by
      simpa only [A, dφ, mul_comm] using H1
    have L2 : (∫ z, g z * ((χ z.1 : ℂ) * (φ z.2 : ℂ)) ∂(volume.prod volume)) =
      ∫ x, (χ x : ℂ) * B x := by
      simpa only [B, cφ, mul_comm] using H2
    rw [L1, L2] at H
    change (∫ x, (χ x) • (A x + B x)) = 0
    simp_rw [Complex.real_smul, mul_add]
    have hIntA : Integrable (fun x => (χ x : ℂ) * A x) := hχL.integrable_mul hA
    have hIntB : Integrable (fun x => (χ x : ℂ) * B x) := hχL.integrable_mul hB
    rw [integral_add hIntA hIntB, H, neg_add_cancel]
  filter_upwards [hzero] with x hx
  simpa only [Pi.add_apply, A, B, fiberContract, dφ, cφ,
    Complex.star_def, Complex.conj_ofReal, mul_comm, add_eq_zero_iff_eq_neg] using hx

lemma weak_slice {u g : E × F → ℂ}
    (hu : MemLp u 2 (volume.prod volume)) (hg : MemLp g 2 (volume.prod volume))
    (v : F)
    (hw : ∀ (η : E × F → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ z, u z * (fderiv ℝ η z (0,v) : ℂ) ∂(volume.prod volume)) =
        -(∫ z, g z * (η z : ℂ) ∂(volume.prod volume))) :
    ∀ᵐ x ∂(volume : Measure E),
      MemLp (fun y => u (x,y)) 2 volume ∧ MemLp (fun y => g (x,y)) 2 volume ∧
      ∀ (φ : F → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ y, u (x,y) * (fderiv ℝ φ y v : ℂ)) = -(∫ y, g (x,y) * (φ y : ℂ)) := by
  classical
  have : Fact ((2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)) := ⟨by norm_num⟩
  have : SecondCountableTopology F :=
    (ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm :
      F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ)).toHomeomorph.secondCountableTopology
  let Tests := {φ : F → ℝ // ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ}
  let Q : Tests → Lp ℂ 2 (volume : Measure F) × Lp ℂ 2 (volume : Measure F) := fun φ =>
    ⟨(test_direction_complex_memLp φ.2.1 φ.2.2 v).toLp _,
      (test_complex_memLp φ.2.1 φ.2.2).toLp _⟩
  let T := Set.range Q
  let U : E → Lp ℂ 2 (volume : Measure F) := fun x =>
    if h : MemLp (fun y => u (x,y)) 2 volume then h.toLp _ else 0
  let G : E → Lp ℂ 2 (volume : Measure F) := fun x =>
    if h : MemLp (fun y => g (x,y)) 2 volume then h.toLp _ else 0
  let A : E → T → ℂ := fun x t => inner ℂ t.1.1 (U x) + inner ℂ t.1.2 (G x)
  have hAc (x : E) : Continuous (A x) :=
    ((continuous_fst.comp continuous_subtype_val).inner continuous_const).add
      ((continuous_snd.comp continuous_subtype_val).inner continuous_const)
  have hAQ (x : E) (hx : MemLp (fun y => u (x,y)) 2 volume)
      (hxg : MemLp (fun y => g (x,y)) 2 volume) (φ : Tests) :
      A x ⟨Q φ, mem_range_self _⟩ =
        (∫ y, u (x,y) * (fderiv ℝ φ.1 y v : ℂ)) + (∫ y, g (x,y) * (φ.1 y : ℂ)) := by
    dsimp only [A, Q]
    simp only [U, G, dite_eq_left hx, dite_eq_left hxg]
    rw [inner_toLp_complex, inner_toLp_complex]
    simp only [Complex.star_def, Complex.conj_ofReal, mul_comm]
  have hAz (t : T) : ∀ᵐ x ∂(volume : Measure E), A x t = 0 := by
    rcases t with ⟨_, φ, rfl⟩
    filter_upwards [memLp_fiber_ae hu, memLp_fiber_ae hg,
      weak_slice_fixed_test hu hg v hw φ.1 φ.2.1 φ.2.2] with x hx hxg hweak
    rw [hAQ x hx hxg φ, hweak, neg_add_cancel]
  have hall := ae_all_zero_of_continuous A hAc hAz
  filter_upwards [memLp_fiber_ae hu, memLp_fiber_ae hg, hall] with x hx hxg hall
  refine ⟨hx, hxg, ?_⟩
  intro φ hφ hφC
  have H := hall ⟨Q ⟨φ, hφ, hφC⟩, mem_range_self _⟩
  rw [hAQ x hx hxg] at H
  exact add_eq_zero_iff_eq_neg.mp H

end SmoothSlices
section LinearChange
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure E} {ν : Measure F}

lemma weak_directional_change {u g : F → ℂ} (L : E ≃L[ℝ] F)
    (hL : MeasurePreserving L.toHomeomorph.toMeasurableEquiv μ ν) (v : E)
    (hw : ∀ (φ : F → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ y, u y * (fderiv ℝ φ y (L v) : ℂ) ∂ν) = -(∫ y, g y * (φ y : ℂ) ∂ν)) :
    ∀ (η : E → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ x, u (L x) * (fderiv ℝ η x v : ℂ) ∂μ) =
        -(∫ x, g (L x) * (η x : ℂ) ∂μ) := by
  intro η hη hηC
  let Φ : F → ℝ := η ∘ L.symm
  have HΦ : ContDiff ℝ (⊤ : ℕ∞) Φ := hη.comp L.symm.contDiff
  have HC : HasCompactSupport Φ := hηC.comp_homeomorph L.symm.toHomeomorph
  have Hd (y : F) : fderiv ℝ Φ y (L v) = fderiv ℝ η (L.symm y) v := by
    dsimp only [Φ]
    rw [fderiv_comp y (hη.differentiable (by simp)).differentiableAt L.symm.differentiableAt,
      show fderiv ℝ (⇑L.symm) y = L.symm.toContinuousLinearMap from
        L.symm.toContinuousLinearMap.fderiv]
    simp
  have H := hw Φ HΦ HC
  simp_rw [Hd] at H
  rw [← hL.integral_comp' (fun y => u y * (fderiv ℝ η (L.symm y) v : ℂ)),
    ← hL.integral_comp' (fun y => g y * (Φ y : ℂ))] at H
  simpa [Φ] using H
end LinearChange

lemma H1Vector.weak_partial_join {m k : ℕ} (ψ : H1Vector (m+k))
    (s : Spins (m+k)) (a : Fin k × Fin 3) :
    ∀ (η : Configuration m × Configuration k → ℝ), ContDiff ℝ (⊤ : ℕ∞) η →
      HasCompactSupport η →
      (∫ z, ψ.value s (joinConfiguration m k z) *
        (fderiv ℝ η z (0, EuclideanSpace.single a 1) : ℂ) ∂(volume.prod volume)) =
      -(∫ z, ψ.gradient s (Fin.natAdd m a.1, a.2) (joinConfiguration m k z) *
        (η z : ℂ) ∂(volume.prod volume)) := by
  apply weak_directional_change (joinConfiguration m k) (joinConfiguration_measurePreserving m k)
    (0, EuclideanSpace.single a 1)
  rw [joinConfiguration_right_single]
  exact ψ.weak_partial s (Fin.natAdd m a.1, a.2)

lemma H1Vector.core_slices_H1 {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    ∀ᵐ x ∂(volume : Measure (Configuration m)),
      (∀ t : Spins k, MemLp (fun y => ψ.value (Fin.append s t) (joinConfiguration m k (x,y))) 2 volume) ∧
      (∀ (t : Spins k) (a : Fin k × Fin 3),
        MemLp (fun y => ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
          (joinConfiguration m k (x,y))) 2 volume ∧
        ∀ (φ : Configuration k → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ y, ψ.value (Fin.append s t) (joinConfiguration m k (x,y)) *
          (fderiv ℝ φ y (EuclideanSpace.single a 1) : ℂ)) =
        -(∫ y, ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
          (joinConfiguration m k (x,y)) * (φ y : ℂ))) := by
  have hV (t : Spins k) := (ψ.value_L2 (Fin.append s t)).comp_measurePreserving
    (joinConfiguration_measurePreserving m k)
  have hG (t : Spins k) (a : Fin k × Fin 3) :=
    (ψ.partial_L2 (Fin.append s t) (Fin.natAdd m a.1,a.2)).comp_measurePreserving
      (joinConfiguration_measurePreserving m k)
  have hval : ∀ᵐ x ∂(volume : Measure (Configuration m)),
      ∀ t : Spins k, MemLp (fun y => ψ.value (Fin.append s t) (joinConfiguration m k (x,y))) 2 volume :=
    ae_all_iff.mpr (fun t => memLp_fiber_ae
      (f := fun z : Configuration m × Configuration k =>
        ψ.value (Fin.append s t) (joinConfiguration m k z)) (hV t))
  have hgrad := fun (t : Spins k) (a : Fin k × Fin 3) =>
    weak_slice (hV t) (hG t a) (EuclideanSpace.single a 1)
      (ψ.weak_partial_join (Fin.append s t) a)
  have hall := ae_all_iff.mpr (fun t => ae_all_iff.mpr (hgrad t))
  filter_upwards [hval, hall] with x hx hall
  exact ⟨hx, fun t a => (hall t a).2⟩

def H1Vector.CoreSliceRegular {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    (x : Configuration m) : Prop :=
      (∀ t : Spins k, MemLp (fun y => ψ.value (Fin.append s t) (joinConfiguration m k (x,y))) 2 volume) ∧
      (∀ (t : Spins k) (a : Fin k × Fin 3),
        MemLp (fun y => ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
          (joinConfiguration m k (x,y))) 2 volume ∧
        ∀ (φ : Configuration k → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ y, ψ.value (Fin.append s t) (joinConfiguration m k (x,y)) *
          (fderiv ℝ φ y (EuclideanSpace.single a 1) : ℂ)) =
        -(∫ y, ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
          (joinConfiguration m k (x,y)) * (φ y : ℂ)))

lemma H1Vector.coreSliceRegular_ae {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    ∀ᵐ x ∂volume, ψ.CoreSliceRegular s x := ψ.core_slices_H1 s

noncomputable def H1Vector.zero (n : ℕ) : H1Vector n where
  value := fun _ _ => 0
  gradient := fun _ _ _ => 0
  value_L2 := fun _ => MemLp.zero'
  partial_L2 := fun _ _ => MemLp.zero'
  weak_partial := by intros; simp

noncomputable def H1Vector.coreSlice {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    (x : Configuration m) : H1Vector k := by
  classical
  exact if h : ψ.CoreSliceRegular s x then
    { value := fun t y => ψ.value (Fin.append s t) (joinConfiguration m k (x,y))
      gradient := fun t a y => ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
        (joinConfiguration m k (x,y))
      value_L2 := h.1
      partial_L2 := fun t a => (h.2 t a).1
      weak_partial := fun t a => (h.2 t a).2 }
  else H1Vector.zero k

lemma H1Vector.coreSlice_value {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    {x : Configuration m} (hx : ψ.CoreSliceRegular s x) (t : Spins k) (y : Configuration k) :
    (ψ.coreSlice s x).value t y = ψ.value (Fin.append s t) (joinConfiguration m k (x,y)) := by
  simp [H1Vector.coreSlice, hx]

lemma H1Vector.coreSlice_gradient {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    {x : Configuration m} (hx : ψ.CoreSliceRegular s x) (t : Spins k) (a : Fin k × Fin 3)
    (y : Configuration k) :
    (ψ.coreSlice s x).gradient t a y =
      ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2) (joinConfiguration m k (x,y)) := by
  simp [H1Vector.coreSlice, hx]

lemma mass_coreSlice_ae {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    (fun x => mass (ψ.coreSlice s x)) =ᵐ[volume]
      fun x => ∑ t : Spins k, ∫ y, ‖ψ.value (Fin.append s t) (joinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.coreSliceRegular_ae s] with x hx
  simp only [mass, ψ.coreSlice_value s hx]

lemma mass_coreSlice_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)) := by
  apply Integrable.congr _ (mass_coreSlice_ae ψ s).symm
  apply integrable_finsetSum
  intro t _
  have h := ((ψ.value_L2 (Fin.append s t)).comp_measurePreserving
    (joinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)
  exact h.integral_prod_left

lemma integral_mass_coreSlice {m k : ℕ} (ψ : H1Vector (m+k)) :
    (∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x)) = mass ψ := by
  calc
    _ = ∑ s : Spins m, ∑ t : Spins k, ∫ z, ‖ψ.value (Fin.append s t) z‖^2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [integral_congr_ae (mass_coreSlice_ae ψ s), integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro t _
        have h := ((ψ.value_L2 (Fin.append s t)).comp_measurePreserving
          (joinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)
        change Integrable (fun z : Configuration m × Configuration k =>
          ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) at h
        rw [← integral_prod _ h]
        exact (joinConfiguration_measurePreserving m k).integral_comp'
          (fun z => ‖ψ.value (Fin.append s t) z‖^2)
      · intro t _
        exact (((ψ.value_L2 (Fin.append s t)).comp_measurePreserving
          (joinConfiguration_measurePreserving m k)).integrable_norm_pow
            (p := 2) (by decide)).integral_prod_left
    _ = mass ψ := by
      rw [← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
        ∫ z, ‖ψ.value (Fin.append st.1 st.2) z‖^2)]
      exact Fintype.sum_equiv (Fin.appendEquiv m k) _ _ (fun _ => rfl)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CorePerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

noncomputable def corePerm (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin (m+k)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr (Equiv.refl (Fin m)) p)

lemma corePerm_left (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) (i : Fin m) :
    corePerm m p (Fin.castAdd k i) = Fin.castAdd k i := by
  simp [corePerm]

lemma corePerm_right (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) (i : Fin k) :
    corePerm m p (Fin.natAdd m i) = Fin.natAdd m (p i) := by
  simp [corePerm]

lemma corePerm_sign (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) :
    (corePerm m p).sign = p.sign := by
  simp [corePerm, Equiv.Perm.sign_sumCongr]

lemma append_corePerm {m k : ℕ} (s : Spins m) (t : Spins k) (p : Equiv.Perm (Fin k)) :
    Fin.append s t ∘ corePerm m p = Fin.append s (t ∘ p) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [corePerm_left]
  · intro j
    simp [corePerm_right]

lemma permute_core_join {m k : ℕ} (p : Equiv.Perm (Fin k)) (x : Configuration m)
    (y : Configuration k) :
    permute (corePerm m p) (joinConfiguration m k (x,y)) =
      joinConfiguration m k (x, permute p y) := by
  ext ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    change joinConfiguration m k (x,y) (corePerm m p (Fin.castAdd k j),b) = _
    rw [corePerm_left, joinConfiguration_left, joinConfiguration_left]
  · intro j
    change joinConfiguration m k (x,y) (corePerm m p (Fin.natAdd m j),b) = _
    rw [corePerm_right, joinConfiguration_right, joinConfiguration_right]
    rfl

lemma H1Vector.coreSlice_antisymmetric {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    (hψ : ∀ (p : Equiv.Perm (Fin k)) (t : Spins k),
      ∀ᵐ z ∂volume, ψ.value (Fin.append s t ∘ corePerm m p) (permute (corePerm m p) z) =
        (((corePerm m p).sign : ℤ) : ℂ) * ψ.value (Fin.append s t) z) :
    ∀ᵐ x ∂volume, Antisymmetric (ψ.coreSlice s x) := by
  have h (p : Equiv.Perm (Fin k)) (t : Spins k) :=
    Measure.ae_ae_of_ae_prod ((joinConfiguration_measurePreserving m k).quasiMeasurePreserving.ae (hψ p t))
  have hall := ae_all_iff.mpr (fun p => ae_all_iff.mpr (h p))
  filter_upwards [ψ.coreSliceRegular_ae s, hall] with x hx hxA
  intro p t
  filter_upwards [hxA p t] with y hy
  change ψ.value (Fin.append s t ∘ corePerm m p)
      (permute (corePerm m p) (joinConfiguration m k (x,y))) =
    (((corePerm m p).sign : ℤ) : ℂ) * ψ.value (Fin.append s t)
      (joinConfiguration m k (x,y)) at hy
  simpa only [ψ.coreSlice_value s hx, append_corePerm, corePerm_sign, permute_core_join] using hy

lemma H1Vector.value_eq_zero_of_mass_zero {n : ℕ} (ψ : H1Vector n)
    (hψ : mass ψ = 0) (s : Spins n) : ψ.value s =ᵐ[volume] 0 := by
  have hnon (t : Spins n) : 0 ≤ ∫ x, ‖ψ.value t x‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hz : (∫ x, ‖ψ.value s x‖^2) = 0 := by
    apply le_antisymm _ (hnon s)
    exact hψ ▸ Finset.single_le_sum (fun t _ => hnon t) (Finset.mem_univ s)
  have ha := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖ψ.value s x‖)
    ((ψ.value_L2 s).integrable_norm_pow (p := 2) (by decide))).mp hz
  filter_upwards [ha] with x hx
  simpa using hx

lemma H1Vector.gradient_eq_zero_of_mass_zero {n : ℕ} (ψ : H1Vector n)
    (hψ : mass ψ = 0) (s : Spins n) (a : Fin n × Fin 3) :
    ψ.gradient s a =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((ψ.partial_L2 s a).locallyIntegrable (by norm_num))
  intro φ hφ hφC
  have H := ψ.weak_partial s a φ hφ hφC
  have hv : (∫ x, ψ.value s x *
      (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ψ.value_eq_zero_of_mass_zero hψ s] with x hx
    simp [hx]
  rw [hv, eq_neg_iff_add_eq_zero, zero_add] at H
  simpa only [Complex.real_smul, mul_comm] using H

lemma kinetic_eq_zero_of_mass_zero {n : ℕ} (ψ : H1Vector n)
    (hψ : mass ψ = 0) : kinetic ψ = 0 := by
  have hzero (s : Spins n) (a : Fin n × Fin 3) : ∫ x, ‖ψ.gradient s a x‖^2 = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ψ.gradient_eq_zero_of_mass_zero hψ s a] with x hx
    simp [hx]
  simp [kinetic, hzero]

lemma kinetic_coreSlice_ae {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    (fun x => kinetic (ψ.coreSlice s x)) =ᵐ[volume]
      fun x => (1/2 : ℝ) * ∑ t : Spins k, ∑ a : Fin k × Fin 3,
        ∫ y, ‖ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
          (joinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.coreSliceRegular_ae s] with x hx
  simp only [kinetic, ψ.coreSlice_gradient s hx]

lemma kinetic_coreSlice_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    Integrable (fun x => kinetic (ψ.coreSlice s x)) := by
  apply Integrable.congr _ (kinetic_coreSlice_ae ψ s).symm
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro t _
  apply integrable_finsetSum
  intro a _
  exact (((ψ.partial_L2 (Fin.append s t) (Fin.natAdd m a.1,a.2)).comp_measurePreserving
    (joinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)).integral_prod_left

noncomputable def H1Vector.normalized {n : ℕ} (ψ : H1Vector n) : H1Vector n :=
  ψ.rsmul (Real.sqrt (mass ψ))⁻¹

lemma mass_normalized {n : ℕ} (ψ : H1Vector n) (hψ : 0 < mass ψ) :
    mass ψ.normalized = 1 := by
  rw [H1Vector.normalized, mass_rsmul, inv_pow, Real.sq_sqrt hψ.le, inv_mul_cancel₀ hψ.ne']

lemma Antisymmetric.normalized {n : ℕ} {ψ : H1Vector n} (hψ : Antisymmetric ψ) :
    Antisymmetric ψ.normalized := hψ.rsmul _

lemma kinetic_normalized_weight {n : ℕ} (ψ : H1Vector n) :
    mass ψ * kinetic ψ.normalized = kinetic ψ := by
  have hm : 0 ≤ mass ψ := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  by_cases hz : mass ψ = 0
  · rw [hz, zero_mul, kinetic_eq_zero_of_mass_zero ψ hz]
  · rw [H1Vector.normalized, kinetic_rsmul, inv_pow, Real.sq_sqrt hm, ← mul_assoc,
      mul_inv_cancel₀ hz, one_mul]

noncomputable def potentialForm {n : ℕ} (V : Configuration n → ℝ) (ψ : H1Vector n) : ℝ :=
  ∑ s, ∫ x, V x * ‖ψ.value s x‖^2

lemma potentialForm_rsmul {n : ℕ} (V : Configuration n → ℝ) (ψ : H1Vector n) (t : ℝ) :
    potentialForm V (ψ.rsmul t) = t^2 * potentialForm V ψ := by
  simp only [potentialForm, H1Vector.rsmul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  simp_rw [mul_left_comm (V _) (t^2), integral_const_mul, ← Finset.mul_sum]

lemma potentialForm_eq_zero_of_mass_zero {n : ℕ} (V : Configuration n → ℝ)
    (ψ : H1Vector n) (hψ : mass ψ = 0) : potentialForm V ψ = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  apply integral_eq_zero_of_ae
  filter_upwards [ψ.value_eq_zero_of_mass_zero hψ s] with x hx
  simp [hx]

lemma potentialForm_normalized_weight {n : ℕ} (V : Configuration n → ℝ) (ψ : H1Vector n) :
    mass ψ * potentialForm V ψ.normalized = potentialForm V ψ := by
  have hm : 0 ≤ mass ψ := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  by_cases hz : mass ψ = 0
  · rw [hz, zero_mul, potentialForm_eq_zero_of_mass_zero V ψ hz]
  · rw [H1Vector.normalized, potentialForm_rsmul, inv_pow, Real.sq_sqrt hm, ← mul_assoc,
      mul_inv_cancel₀ hz, one_mul]

lemma potentialForm_coreSlice_ae {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    (V : Configuration k → ℝ) :
    (fun x => potentialForm V (ψ.coreSlice s x)) =ᵐ[volume]
      fun x => ∑ t : Spins k, ∫ y, V y * ‖ψ.value (Fin.append s t) (joinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.coreSliceRegular_ae s] with x hx
  simp only [potentialForm, ψ.coreSlice_value s hx]

lemma potentialForm_coreSlice_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    (V : Configuration k → ℝ)
    (hV : ∀ t : Spins k, Integrable (fun z => V ((joinConfiguration m k).symm z).2 *
      ‖ψ.value (Fin.append s t) z‖^2)) :
    Integrable (fun x => potentialForm V (ψ.coreSlice s x)) := by
  apply Integrable.congr _ (potentialForm_coreSlice_ae ψ s V).symm
  apply integrable_finsetSum
  intro t _
  have H := ((joinConfiguration_measurePreserving m k).integrable_comp_emb
    (joinConfiguration m k).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr (hV t)
  have H' : Integrable (fun z : Configuration m × Configuration k =>
      V z.2 * ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) := by
    change Integrable (fun z : Configuration m × Configuration k =>
      V ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
        ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) at H
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
  exact H'.integral_prod_left

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_MeridianMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb
noncomputable def meridianMap (p : ℝ × ℝ) : ℝ × ℝ := (Real.sqrt (p.1^2-p.2^2), p.2)
def meridianDomain : Set (ℝ × ℝ) := {p | |p.2| < p.1}
lemma meridianDomain_measurable : MeasurableSet meridianDomain :=
  measurableSet_lt (measurable_snd.abs) measurable_fst
lemma meridian_radicand_pos {p : ℝ × ℝ} (hp : p ∈ meridianDomain) : 0 < p.1^2-p.2^2 := by
  change |p.2| < p.1 at hp
  have h0 := abs_nonneg p.2
  nlinarith [sq_abs p.2]
noncomputable def meridianDeriv (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![p.1 / Real.sqrt (p.1^2-p.2^2), -p.2 / Real.sqrt (p.1^2-p.2^2); 0, 1]).toContinuousLinearMap
lemma meridian_hasFDeriv {p : ℝ × ℝ} (hp : p ∈ meridianDomain) :
    HasFDerivAt meridianMap (meridianDeriv p) p := by
  have hf : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hg : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hh := (Real.hasDerivAt_sqrt (meridian_radicand_pos hp).ne').comp_hasFDerivAt p
    ((hf.pow 2).sub (hg.pow 2))
  have h := hh.prodMk (hasFDerivAt_snd (𝕜:=ℝ) (E:=ℝ) (F:=ℝ))
  unfold meridianDeriv
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  apply h.congr_fderiv
  ext <;> simp [div_eq_mul_inv] <;> ring
lemma meridian_det (p : ℝ × ℝ) : (meridianDeriv p).det = p.1 / Real.sqrt (p.1^2-p.2^2) := by
  simp [meridianDeriv, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
lemma meridianMap_injOn : InjOn meridianMap meridianDomain := by
  intro p hp q hq he
  have h1 : Real.sqrt (p.1^2-p.2^2) = Real.sqrt (q.1^2-q.2^2) := congrArg Prod.fst he
  have h2 : p.2 = q.2 := by simpa [meridianMap] using congrArg Prod.snd he
  have hp0 := meridian_radicand_pos hp
  have hq0 := meridian_radicand_pos hq
  rw [Real.sqrt_inj hp0.le hq0.le] at h1
  have hpp : 0 < p.1 := (abs_nonneg p.2).trans_lt hp
  have hqq : 0 < q.1 := (abs_nonneg q.2).trans_lt hq
  apply Prod.ext _ h2
  rw [h2] at h1
  nlinarith
lemma meridian_image : meridianMap '' meridianDomain = Ioi (0:ℝ) ×ˢ (univ : Set ℝ) := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Real.sqrt_pos.mpr (meridian_radicand_pos hp), mem_univ _⟩
  · rintro ⟨hq, _⟩
    change 0 < q.1 at hq
    refine ⟨(Real.sqrt (q.1^2+q.2^2), q.2), ?_, ?_⟩
    · change |q.2| < Real.sqrt (q.1^2+q.2^2)
      rw [Real.lt_sqrt (abs_nonneg _)]
      nlinarith [sq_abs q.2, sq_pos_of_pos hq]
    · apply Prod.ext
      · dsimp [meridianMap]
        rw [Real.sq_sqrt (by positivity), add_sub_cancel_right, Real.sqrt_sq hq.le]
      · rfl

lemma meridian_lintegral (f : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ q in Ioi (0:ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal q.1 * f q) =
      ∫⁻ p in meridianDomain, ENNReal.ofReal p.1 * f (meridianMap p) := by
  rw [← meridian_image, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    meridianDomain_measurable (fun p hp => (meridian_hasFDeriv hp).hasFDerivWithinAt) meridianMap_injOn]
  apply setLIntegral_congr_fun meridianDomain_measurable
  intro p hp
  have hr := meridian_radicand_pos hp
  have hs := Real.sqrt_pos.mpr hr
  have hp0 : 0 < p.1 := (abs_nonneg p.2).trans_lt hp
  dsimp only
  rw [meridian_det, abs_of_pos (div_pos hp0 hs)]
  change ENNReal.ofReal (p.1 / Real.sqrt (p.1^2-p.2^2)) *
    (ENNReal.ofReal (Real.sqrt (p.1^2-p.2^2)) * f _) = _
  rw [← mul_assoc, ← ENNReal.ofReal_mul (div_pos hp0 hs).le, div_mul_cancel₀ _ hs.ne']

lemma plane_radial_lintegral (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q : ℝ × ℝ, F (Real.sqrt (q.1^2+q.2^2))) =
      ENNReal.ofReal (2*Real.pi) * ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal r * F r := by
  rw [← lintegral_comp_polarCoord_symm]
  have hpoint (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
      Real.sqrt ((polarCoord.symm p).1^2+(polarCoord.symm p).2^2) = p.1 := by
    have hr : 0 < p.1 := hp.1
    dsimp [polarCoord]
    rw [show (p.1 * Real.cos p.2)^2 + (p.1 * Real.sin p.2)^2 = p.1^2 from by
      nlinarith [Real.sin_sq_add_cos_sq p.2]]
    exact Real.sqrt_sq hr.le
  calc
    _ = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 * F p.1 := by
      apply setLIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      simp only [smul_eq_mul, hpoint p hp]
    _ = _ := by
      change (∫⁻ p : ℝ × ℝ in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * F p.1) = _
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
      · simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_neg_eq_add]
        rw [show Real.pi + Real.pi = 2*Real.pi by ring, lintegral_mul_const]
        · exact mul_comm _ _
        · exact measurable_id.ennreal_ofReal.mul hF
      · exact ((measurable_fst.ennreal_ofReal).mul (hF.comp measurable_fst)).aemeasurable

lemma axisymmetric_lintegral (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z : ℝ, ∫⁻ q : ℝ × ℝ, F (Real.sqrt (z^2+q.1^2+q.2^2), z)) =
      ENNReal.ofReal (2*Real.pi) *
        ∫⁻ p in meridianDomain, ENNReal.ofReal p.1 * F p := by
  have hp (z : ℝ) := plane_radial_lintegral
    (fun r => F (Real.sqrt (z^2+r^2), z))
    (hF.comp (((measurable_const.add (measurable_id.pow_const 2)).sqrt).prodMk measurable_const))
  have he (z : ℝ) : (∫⁻ q : ℝ × ℝ, F (Real.sqrt (z^2+q.1^2+q.2^2), z)) =
      ENNReal.ofReal (2*Real.pi) *
        ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal r * F (Real.sqrt (r^2+z^2), z) := by
    convert hp z using 1
    · apply lintegral_congr
      intro q
      rw [Real.sq_sqrt (by positivity)]
      congr 3
      ring
    · congr 1
      apply lintegral_congr
      intro r
      rw [add_comm (z^2) (r^2)]
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * F (Real.sqrt (p.1^2+p.2^2), p.2)) := by
    exact measurable_fst.ennreal_ofReal.mul
      (hF.comp (((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).sqrt.prodMk measurable_snd))
  rw [← lintegral_lintegral_swap hm.aemeasurable]
  rw [← lintegral_prod _ hm.aemeasurable]
  rw [show (volume.restrict (Ioi (0:ℝ))).prod volume =
    (volume : Measure (ℝ × ℝ)).restrict (Ioi (0:ℝ) ×ˢ univ) from by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]]
  rw [meridian_lintegral]
  apply setLIntegral_congr_fun meridianDomain_measurable
  intro p hp
  dsimp [meridianMap]
  rw [Real.sq_sqrt (meridian_radicand_pos hp).le, sub_add_cancel,
    Real.sqrt_sq ((abs_nonneg p.2).trans_lt hp).le]

lemma meridian_lintegral_iterated (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p in meridianDomain, ENNReal.ofReal p.1 * F p) =
      ∫⁻ s in Ioi (0:ℝ), ∫⁻ z in Ioo (-s) s, ENNReal.ofReal s * F (s,z) := by
  have hm : Measurable (meridianDomain.indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * F p)) :=
    (measurable_fst.ennreal_ofReal.mul hF).indicator meridianDomain_measurable
  rw [← lintegral_indicator meridianDomain_measurable, Measure.volume_eq_prod,
    lintegral_prod _ hm.aemeasurable, ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro s
  by_cases hs : 0 < s
  · rw [Set.indicator_of_mem (show s ∈ Ioi (0:ℝ) from hs), ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro z
    have he : (s,z) ∈ meridianDomain ↔ z ∈ Ioo (-s) s := by
      change |z| < s ↔ -s < z ∧ z < s
      exact abs_lt
    by_cases hz : z ∈ Ioo (-s) s <;> simp [Set.indicator, he, hz]
  · rw [Set.indicator_of_notMem (show s ∉ Ioi (0:ℝ) from hs)]
    simp [Set.indicator, ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hs)]

noncomputable def tripleSpaceEquiv : (ℝ × (ℝ × ℝ)) ≃ᵐ Space :=
  ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun _ => ℝ)).symm).trans
    (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm).trans
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)))
lemma tripleSpaceEquiv_apply (p : ℝ × (ℝ × ℝ)) :
    tripleSpaceEquiv p = WithLp.toLp 2 ![p.1,p.2.1,p.2.2] := by
  ext i
  fin_cases i <;> rfl
lemma tripleSpaceEquiv_preserving : MeasurePreserving tripleSpaceEquiv volume volume := by
  have h1 := (MeasurePreserving.id (volume : Measure ℝ)).prod
    ((volume_preserving_piFinTwo (fun _ => ℝ)).symm _)
  have h2 := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm _
  have h3 := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm _
  exact h3.comp (h2.comp h1)
lemma norm_tripleSpaceEquiv (p : ℝ × (ℝ × ℝ)) :
    ‖tripleSpaceEquiv p‖ = Real.sqrt (p.1^2 + p.2.1^2+p.2.2^2) := by
  rw [tripleSpaceEquiv_apply, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc]
lemma axisymmetric_space_lintegral (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x : Space, F (‖x‖, x 0)) = ENNReal.ofReal (2*Real.pi) *
      ∫⁻ p in meridianDomain, ENNReal.ofReal p.1 * F p := by
  rw [← tripleSpaceEquiv_preserving.lintegral_comp_emb tripleSpaceEquiv.measurableEmbedding,
    Measure.volume_eq_prod, lintegral_prod]
  · simp only [norm_tripleSpaceEquiv]
    have he (p : ℝ × (ℝ × ℝ)) : tripleSpaceEquiv p 0 = p.1 := by
      rw [tripleSpaceEquiv_apply]; rfl
    simp_rw [he]
    exact axisymmetric_lintegral F hF
  · have hm : Measurable (fun x : Space => F (‖x‖, x 0)) :=
      hF.comp (measurable_norm.prodMk (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).measurable)
    exact (hm.comp tripleSpaceEquiv.measurable).aemeasurable

lemma angular_coulomb_integral {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (1/2:ℝ) * (∫ u in (-1:ℝ)..1, (r^2+s^2-2*r*s*u)^(-(1/2):ℝ)) = (max r s)⁻¹ := by
  have H := intervalIntegral.mul_integral_comp_sub_mul (f := fun x : ℝ => x^(-(1/2):ℝ))
    (a := -1) (b := 1) (2*r*s) (r^2+s^2)
  have h1 : r^2+s^2-(2*r*s)*1 = (r-s)^2 := by ring
  have h2 : r^2+s^2-(2*r*s)*(-1) = (r+s)^2 := by ring
  rw [h1, h2, integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/2)))] at H
  norm_num only [show (-(1/2):ℝ)+1 = 1/2 by norm_num] at H
  simp_rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs] at H
  rw [abs_of_pos (add_pos hr hs)] at H
  rcases le_total r s with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)] at *
    field_simp
    nlinarith
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)] at *
    field_simp
    nlinarith

lemma affine_halfpower_intervalIntegrable (d c a b : ℝ) (hc : c ≠ 0) :
    IntervalIntegrable (fun z => (d-c*z)^(-(1/2):ℝ)) volume a b := by
  have H := ((intervalIntegral.intervalIntegrable_rpow'
    (a:=d-c*a) (b:=d-c*b) (by norm_num : (-1:ℝ) < -(1/2))).comp_sub_left d).comp_mul_left (c:=c)
  convert H using 1 <;> field_simp <;> ring

lemma meridian_coulomb_integral {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∫ z in (-s)..s, (r^2+s^2-2*r*z)^(-(1/2):ℝ)) = 2*s*(max r s)⁻¹ := by
  have H := intervalIntegral.integral_comp_mul_left (a:=(-1:ℝ)) (b:=1)
    (c:=s) (fun z => (r^2+s^2-2*r*z)^(-(1/2):ℝ)) hs.ne'
  have he (u : ℝ) : r^2+s^2-2*r*(s*u) = r^2+s^2-2*r*s*u := by ring
  simp_rw [he] at H
  simp only [mul_neg_one, mul_one, smul_eq_mul] at H
  have A := angular_coulomb_integral hr hs
  rw [H] at A
  have hsi : s*s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  calc
    _ = s * (s⁻¹ * ∫ z in (-s)..s, (r^2+s^2-2*r*z)^(-(1/2):ℝ)) := by rw [← mul_assoc, hsi, one_mul]
    _ = _ := by nlinarith

lemma meridian_coulomb_lintegral {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∫⁻ z in Ioo (-s) s, ENNReal.ofReal ((r^2+s^2-2*r*z)^(-(1/2):ℝ))) =
      ENNReal.ofReal (2*s*(max r s)⁻¹) := by
  have hab : -s ≤ s := by linarith
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp
    (affine_halfpower_intervalIntegrable (r^2+s^2) (2*r) (-s) s (by positivity))
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hab,
      meridian_coulomb_integral hr hs]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact Real.rpow_nonneg (by nlinarith [sq_nonneg (r-s), hz.2]) _

lemma norm_axis_sub_rpow (r : ℝ) (x : Space) :
    ‖EuclideanSpace.single 0 r - x‖⁻¹ =
      (r^2+‖x‖^2-2*r*x 0)^(-(1/2):ℝ) := by
  have he : ‖EuclideanSpace.single 0 r - x‖^2 = r^2+‖x‖^2-2*r*x 0 := by
    rw [norm_sub_sq_real]
    simp [EuclideanSpace.inner_single_left, Real.norm_eq_abs, sq_abs]
    ring
  rw [← he, Real.rpow_neg (sq_nonneg _) (1/2:ℝ), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg _)]

lemma radial_axis_coulomb_lintegral (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ x : Space, ENNReal.ofReal ‖EuclideanSpace.single 0 r-x‖⁻¹ * F ‖x‖) =
      ENNReal.ofReal (4*Real.pi) *
        ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s^2*(max r s)⁻¹) * F s := by
  simp_rw [norm_axis_sub_rpow]
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((r^2+p.1^2-2*r*p.2)^(-(1/2):ℝ)) * F p.1) := by fun_prop
  rw [axisymmetric_space_lintegral _ hm, meridian_lintegral_iterated _ hm]
  have he (s : ℝ) (hs : s ∈ Ioi (0:ℝ)) :
      (∫⁻ z in Ioo (-s) s, ENNReal.ofReal s *
        (ENNReal.ofReal ((r^2+s^2-2*r*z)^(-(1/2):ℝ)) * F s)) =
      ENNReal.ofReal 2 * (ENNReal.ofReal (s^2*(max r s)⁻¹) * F s) := by
    change 0 < s at hs
    rw [lintegral_const_mul _ (by fun_prop), lintegral_mul_const _ (by fun_prop),
      meridian_coulomb_lintegral hr hs]
    calc
      _ = ENNReal.ofReal (s*(2*s*(max r s)⁻¹))*F s := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hs.le]
      _ = ENNReal.ofReal (2*(s^2*(max r s)⁻¹))*F s := by congr 2; ring
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), mul_assoc]
  rw [setLIntegral_congr_fun measurableSet_Ioi he, lintegral_const_mul _ (by fun_prop),
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

lemma radial_space_lintegral (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x : Space, F ‖x‖) = ENNReal.ofReal (4*Real.pi) *
      ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s^2) * F s := by
  have hm : Measurable (fun p : ℝ × ℝ => F p.1) := hF.comp measurable_fst
  rw [axisymmetric_space_lintegral _ hm, meridian_lintegral_iterated _ hm]
  have he (s : ℝ) (hs : s ∈ Ioi (0:ℝ)) :
      (∫⁻ z in Ioo (-s) s, ENNReal.ofReal s * F s) =
      ENNReal.ofReal 2 * (ENNReal.ofReal (s^2) * F s) := by
    change 0 < s at hs
    simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
    rw [show s- -s = 2*s by ring, mul_comm (ENNReal.ofReal s * F s),
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 2
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi he, lintegral_const_mul _ (by fun_prop),
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

lemma radial_coulomb_lintegral (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    {x : Space} (hx : x ≠ 0) :
    (∫⁻ y : Space, ENNReal.ofReal ‖x-y‖⁻¹ * F ‖y‖) =
      ENNReal.ofReal (4*Real.pi) *
        ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s^2*(max ‖x‖ s)⁻¹) * F s := by
  let v : Space := EuclideanSpace.single 0 ‖x‖
  let E := (ℝ ∙ (v-x))ᗮ.reflection
  have hv : ‖v‖ = ‖x‖ := by simp [v]
  have hE : E v = x := Submodule.reflection_sub hv
  calc
    _ = ∫⁻ y : Space, ENNReal.ofReal ‖x-E y‖⁻¹ * F ‖E y‖ :=
      (E.measurePreserving.lintegral_comp_emb E.toHomeomorph.measurableEmbedding _).symm
    _ = ∫⁻ y : Space, ENNReal.ofReal ‖v-y‖⁻¹ * F ‖y‖ := by
      apply lintegral_congr
      intro y
      rw [← hE, ← E.map_sub, E.norm_map, E.norm_map]
    _ = _ := radial_axis_coulomb_lintegral F hF (norm_pos_iff.mpr hx)

lemma radial_coulomb_lintegral_eq (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    {R : ℝ} (hFR : ∀ s, R < s → F s = 0)
    {x : Space} (hx : x ≠ 0) (hRx : R ≤ ‖x‖) :
    (∫⁻ y : Space, ENNReal.ofReal ‖x-y‖⁻¹ * F ‖y‖) =
      ENNReal.ofReal ‖x‖⁻¹ * ∫⁻ y : Space, F ‖y‖ := by
  calc
    _ = ENNReal.ofReal (4*Real.pi) *
        ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s^2*(max ‖x‖ s)⁻¹) * F s :=
      radial_coulomb_lintegral F hF hx
    _ = ENNReal.ofReal (4*Real.pi) *
        ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (‖x‖⁻¹*s^2) * F s := by
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s _
      dsimp only
      by_cases hs : R < s
      · simp [hFR s hs]
      · rw [max_eq_left ((le_of_not_gt hs).trans hRx), mul_comm (s^2)]
    _ = _ := by
      rw [radial_space_lintegral F hF]
      simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg x)), mul_assoc]
      rw [lintegral_const_mul _ (by fun_prop)]
      ac_rfl

lemma space_axis_continuous : Continuous (fun s : ℝ => (EuclideanSpace.single (0 : Fin 3) s : Space)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  simp only [Pi.single_apply]
  split <;> fun_prop

lemma radial_coulomb_integral_eq {f : Space → ℝ} (hf : Integrable f)
    (hm : Measurable f) (hf0 : ∀ y, 0 ≤ f y) {M : ℝ} (hfM : ∀ y, f y ≤ M)
    (hrad : ∀ y, f y = f (EuclideanSpace.single 0 ‖y‖))
    {R : ℝ} (hR : 0 ≤ R) (hfs : ∀ y, R < ‖y‖ → f y = 0)
    {x : Space} (hx : x ≠ 0) (hRx : R ≤ ‖x‖) :
    (∫ y, coulombKernel (x-y) * f y) = coulombKernel x * ∫ y, f y := by
  let F : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (f (EuclideanSpace.single 0 s))
  have hmF : Measurable F := (hm.comp space_axis_continuous.measurable).ennreal_ofReal
  have he (y : Space) : F ‖y‖ = ENNReal.ofReal (f y) := congrArg ENNReal.ofReal (hrad y).symm
  have hs : ∀ s, R < s → F s = 0 := by
    intro s hs
    have hsp : 0 < s := hR.trans_lt hs
    have h := hfs (EuclideanSpace.single 0 s) (by simpa [Real.norm_eq_abs, abs_of_pos hsp] using hs)
    simp only [F, h, ENNReal.ofReal_zero]
  have H := radial_coulomb_lintegral_eq F hmF hs hx hRx
  simp_rw [he] at H
  have hi := coulomb_convolution_integrable hf hm hf0 hfM (by norm_num : (0:ℝ) < 1) x
  have hp (y : Space) : 0 ≤ coulombKernel (x-y)*f y := mul_nonneg (coulombKernel_nonneg _) (hf0 _)
  have hI := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hp)
  have hmass := ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hf0)
  simp_rw [ENNReal.ofReal_mul (coulombKernel_nonneg _)] at hI
  change ENNReal.ofReal (∫ y, coulombKernel (x-y)*f y) =
    ∫⁻ y, ENNReal.ofReal ‖x-y‖⁻¹*ENNReal.ofReal (f y) at hI
  rw [← hI, ← hmass, ← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _))] at H
  change ENNReal.ofReal (∫ y, coulombKernel (x-y)*f y) =
    ENNReal.ofReal (coulombKernel x * ∫ y, f y) at H
  have H' := congrArg ENNReal.toReal H
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hp),
    ENNReal.toReal_ofReal (mul_nonneg (coulombKernel_nonneg x) (integral_nonneg hf0))] using H'

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CoulombBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
namespace Coulomb
noncomputable def coulombBilinear (f g : Space → ℝ) : ℝ :=
  ∫ p : Space × Space, f p.1*g p.2*coulombKernel (p.1-p.2)

lemma coulombBilinear_iterated {f g : Space → ℝ} (hf : Integrable f) (hfm : Measurable f)
    (hg : Integrable g) (hgm : Measurable g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) :
    coulombBilinear f g = ∫ x, f x*(∫ y, coulombKernel (x-y)*g y) := by
  unfold coulombBilinear
  change (∫ p : Space × Space, f p.1*g p.2*coulombKernel (p.1-p.2) ∂volume.prod volume) = _
  rw [integral_prod _ (coulomb_pair_integrable hf hfm hg hgm hM)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by ring))

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FrameOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
namespace Coulomb
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]
noncomputable def frameOperator (μ : Measure X) (v : X → E) : E →L[ℂ] E :=
  ∫ x, InnerProductSpace.rankOne ℂ (v x) (v x) ∂μ
omit [CompleteSpace E] in
lemma rankOne_self_continuous : Continuous (fun z : E => InnerProductSpace.rankOne ℂ z z) := by
  change Continuous (fun z : E => (innerSL ℂ z).smulRight z)
  exact (ContinuousLinearMap.smulRightL ℂ E E).continuous₂.comp₂
    (innerSL ℂ).continuous continuous_id
omit [CompleteSpace E] in
lemma rankOne_integrable {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) :
    Integrable (fun x => InnerProductSpace.rankOne ℂ (v x) (v x)) μ := by
  have hm : AEStronglyMeasurable (fun x => InnerProductSpace.rankOne ℂ (v x) (v x)) μ :=
    rankOne_self_continuous.comp_aestronglyMeasurable hv.aestronglyMeasurable
  exact (hv.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).mono' hm
    (Filter.Eventually.of_forall fun x => by simp [pow_two])
omit [CompleteSpace E] in
lemma frameOperator_apply {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) (u : E) :
    frameOperator μ v u = ∫ x, inner ℂ (v x) u • v x ∂μ := by
  rw [frameOperator,ContinuousLinearMap.integral_apply (rankOne_integrable hv)]
  rfl
lemma frameOperator_inner {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) (u w : E) :
    inner ℂ u (frameOperator μ v w) = ∫ x,inner ℂ u (v x)*inner ℂ (v x) w ∂μ := by
  have hi : Integrable (fun x => inner ℂ (v x) w • v x) μ :=
    (ContinuousLinearMap.apply ℂ E w).integrable_comp (rankOne_integrable hv)
  rw [frameOperator_apply hv]
  change (innerSL ℂ u) (∫ x,inner ℂ (v x) w • v x ∂μ) = _
  rw [←(innerSL ℂ u).integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [mul_comm]
lemma frameOperator_quadratic {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) (u : E) :
    (inner ℂ u (frameOperator μ v u)).re = ∫ x,‖inner ℂ (v x) u‖^2 ∂μ := by
  have hi := ((innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ E u)).integrable_comp
    (rankOne_integrable hv)
  have hi' : Integrable (fun x => inner ℂ u (v x)*inner ℂ (v x) u) μ := by
    simpa [ContinuousLinearMap.comp_apply,inner_smul_right,mul_comm] using hi
  rw [frameOperator_inner hv]
  change RCLike.re (∫ x,inner ℂ u (v x)*inner ℂ (v x) u ∂μ) = _
  rw [←integral_re hi']
  apply integral_congr_ae
  filter_upwards [] with x
  rw [←inner_conj_symm u (v x),←Complex.normSq_eq_conj_mul_self]
  exact (Complex.sq_norm _).symm
lemma frameOperator_nonneg {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) (u : E) :
    0 ≤ (inner ℂ u (frameOperator μ v u)).re := by
  rw [frameOperator_quadratic hv]
  exact integral_nonneg (fun x => sq_nonneg _)
omit [CompleteSpace E] in
lemma rankOne_compact (v w : E) : IsCompactOperator (InnerProductSpace.rankOne ℂ v w) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ v)).comp_clm (innerSL ℂ w)
lemma integral_mem_closed_submodule {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {μ : Measure X} {f : X → F} (S : Submodule ℂ F)
    (hS : IsClosed (S : Set F)) (hf : Integrable f μ) (hmem : ∀ᵐ x ∂μ, f x ∈ S) :
    (∫ x,f x ∂μ) ∈ S := by
  let : Fact (IsClosed (S : Set F)) := ⟨hS⟩
  apply (Submodule.Quotient.mk_eq_zero S).mp
  change S.mkQL (∫ x,f x ∂μ) = 0
  rw [←S.mkQL.integral_comp_comm hf]
  apply integral_eq_zero_of_ae
  filter_upwards [hmem] with x hx
  exact (Submodule.Quotient.mk_eq_zero S).mpr hx
lemma frameOperator_compact {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) :
    IsCompactOperator (frameOperator μ v) := by
  exact integral_mem_closed_submodule (compactOperator (RingHom.id ℂ) E E)
    isClosed_setOfPred_isCompactOperator (rankOne_integrable hv)
    (Filter.Eventually.of_forall fun x => rankOne_compact (v x) (v x))
lemma frameOperator_symmetric {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) :
    (frameOperator μ v).toLinearMap.IsSymmetric := by
  intro u w
  change inner ℂ (frameOperator μ v u) w = inner ℂ u (frameOperator μ v w)
  rw [←inner_conj_symm (frameOperator μ v u) w,frameOperator_inner hv,frameOperator_inner hv]
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [map_mul,inner_conj_symm,mul_comm]
lemma frameOperator_positive {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) :
    (frameOperator μ v).toLinearMap.IsPositive := by
  refine ⟨frameOperator_symmetric hv,fun u => ?_⟩
  change 0 ≤ RCLike.re (inner ℂ (frameOperator μ v u) u)
  rw [inner_re_symm]
  exact frameOperator_nonneg hv u
end Coulomb

open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_EigenspaceBasisSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
namespace Coulomb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
noncomputable def eigenspaceBasisSet (T : E →L[ℂ] E) (z : ℂ) : Set (eigenspace T.toLinearMap z) := by
  letI : CompleteSpace (eigenspace T.toLinearMap z) :=
    (T.isClosed_eigenspace z).isComplete.completeSpace_coe
  exact (exists_hilbertBasis ℂ (eigenspace T.toLinearMap z)).choose
noncomputable def eigenspaceHilbertBasis (T : E →L[ℂ] E) (z : ℂ) :
    HilbertBasis (eigenspaceBasisSet T z) ℂ (eigenspace T.toLinearMap z) := by
  letI : CompleteSpace (eigenspace T.toLinearMap z) :=
    (T.isClosed_eigenspace z).isComplete.completeSpace_coe
  exact (exists_hilbertBasis ℂ (eigenspace T.toLinearMap z)).choose_spec.choose
noncomputable def spectralVectors (T : E →L[ℂ] E) (i : Σ z, eigenspaceBasisSet T z) : E :=
  eigenspaceHilbertBasis T i.1 i.2
lemma spectralVectors_orthonormal (T : E →L[ℂ] E) (hT : T.IsSymmetric) :
    Orthonormal ℂ (spectralVectors T) :=
  hT.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
    (fun z => (eigenspaceHilbertBasis T z).orthonormal)
lemma spectralVectors_eigen (T : E →L[ℂ] E) (i : Σ z, eigenspaceBasisSet T z) :
    T (spectralVectors T i) = i.1 • spectralVectors T i :=
  (mem_eigenspace_iff).mp (eigenspaceHilbertBasis T i.1 i.2).property
lemma spectralVectors_orthogonal_eq_bot (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hT : T.IsSymmetric) :
    (Submodule.span ℂ (Set.range (spectralVectors T)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hx' : x ∈ (⨆ z, eigenspace T.toLinearMap z)ᗮ := by
    rw [←Submodule.iInf_orthogonal]
    rw [Submodule.mem_iInf]
    intro z
    rw [Submodule.mem_orthogonal']
    intro v hv
    let v' : eigenspace T.toLinearMap z := ⟨v,hv⟩
    have hs := (eigenspaceHilbertBasis T z).hasSum_repr v'
    have he : ∀ i : eigenspaceBasisSet T z,
        inner ℂ x ((eigenspaceHilbertBasis T z i : eigenspace T.toLinearMap z) : E) = 0 := by
      intro i
      exact ((Submodule.mem_orthogonal' _ _).mp hx) _
        (Submodule.subset_span (Set.mem_range.mpr ⟨⟨z,i⟩,rfl⟩))
    have hsum := (hs.mapL (eigenspace T.toLinearMap z).subtypeL).mapL (innerSL ℂ x)
    have hz : HasSum (fun _ : eigenspaceBasisSet T z => (0:ℂ)) (inner ℂ x v) := by
      simpa only [ContinuousLinearMap.map_smul,Submodule.subtypeL_apply,
        innerSL_apply_apply,he,smul_zero] using hsum
    exact hz.unique hasSum_zero
  simpa only [T.orthogonalComplement_iSup_eigenspaces_eq_bot hc hT] using hx'
noncomputable def compactSpectralBasis (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hT : T.IsSymmetric) :
    HilbertBasis (Σ z, eigenspaceBasisSet T z) ℂ E :=
  HilbertBasis.mkOfOrthogonalEqBot (spectralVectors_orthonormal T hT)
    (spectralVectors_orthogonal_eq_bot T hc hT)
lemma compactSpectralBasis_eigen (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hT : T.IsSymmetric) (i : Σ z, eigenspaceBasisSet T z) :
    T (compactSpectralBasis T hc hT i) = i.1 • compactSpectralBasis T hc hT i := by
  simpa only [compactSpectralBasis,HilbertBasis.coe_mkOfOrthogonalEqBot] using spectralVectors_eigen T i
omit [CompleteSpace E] in
lemma orthonormal_countable {ι : Type*} [SeparableSpace E] {v : ι → E}
    (hv : Orthonormal ℂ v) : Countable ι := by
  have hd : Pairwise (Disjoint on (fun i => Metric.ball (v i) (1/2:ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hs : ‖v i-v j‖^2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), hv.1 i, hv.1 j, hv.2 hij]
      norm_num
    rw [dist_eq_norm]
    have hn := norm_nonneg (v i-v j)
    nlinarith
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i,by simp⟩)
lemma compactSpectralBasis_eigen_real (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hT : T.IsSymmetric) (i : Σ z, eigenspaceBasisSet T z) :
    i.1.im = 0 := by
  have h := hT.im_inner_self_apply (compactSpectralBasis T hc hT i)
  simpa [compactSpectralBasis_eigen,inner_smul_right,inner_self_eq_norm_sq_to_K,
    (compactSpectralBasis T hc hT).orthonormal.1 i] using h
lemma compactSpectralBasis_eigen_nonneg (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hT : T.toLinearMap.IsPositive) (i : Σ z, eigenspaceBasisSet T z) :
    0 ≤ i.1.re := by
  have h := hT.re_inner_nonneg_right (compactSpectralBasis T hc hT.1 i)
  simpa [compactSpectralBasis_eigen,inner_smul_right,inner_self_eq_norm_sq_to_K,
    (compactSpectralBasis T hc hT.1).orthonormal.1 i] using h
end Coulomb

open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_HilbertBasisSumSqInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
namespace Coulomb
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma hilbertBasis_hasSum_sq_inner {ι : Type*} (b : HilbertBasis ι ℂ E) (u : E) :
    HasSum (fun i => ‖inner ℂ (b i) u‖^2) (‖u‖^2) := by
  have h := (b.hasSum_inner_mul_inner u u).mapL Complex.reCLM
  convert h using 1
  · ext i
    rw [← inner_conj_symm u (b i), ← Complex.normSq_eq_conj_mul_self]
    simpa only [Complex.reCLM_apply, Complex.ofReal_re] using Complex.sq_norm (inner ℂ (b i) u)
  · rw [inner_self_eq_norm_sq_to_K]
    change ‖u‖^2 = ((‖u‖ : ℂ)^2).re
    rw [← Complex.ofReal_pow, Complex.ofReal_re]

lemma frameOperator_hasSum_diagonal {ι : Type*} [Countable ι]
    {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) (b : HilbertBasis ι ℂ E) :
    HasSum (fun i => (inner ℂ (b i) (frameOperator μ v (b i))).re)
      (∫ x, ‖v x‖^2 ∂μ) := by
  have hs (x : X) := hilbertBasis_hasSum_sq_inner b (v x)
  have hh : HasSum (fun i => ∫ x, ‖inner ℂ (b i) (v x)‖^2 ∂μ)
      (∫ x, ‖v x‖^2 ∂μ) := by
    apply hasSum_integral_of_dominated_convergence (fun i x => ‖inner ℂ (b i) (v x)‖^2)
    · intro i
      exact (((innerSL ℂ (b i)).continuous.comp_aestronglyMeasurable hv.aestronglyMeasurable).norm.pow 2)
    · intro i
      exact Filter.Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (sq_nonneg _)])
    · exact Filter.Eventually.of_forall (fun x => (hs x).summable)
    · simp_rw [(hs _).tsum_eq]
      exact hv.integrable_norm_pow (by norm_num)
    · exact Filter.Eventually.of_forall hs
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext i
  rw [frameOperator_quadratic hv]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [norm_inner_symm]

lemma frameOperator_spectral_hasSum [SeparableSpace E]
    {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) :
    HasSum (fun i : Σ z, eigenspaceBasisSet (frameOperator μ v) z => i.1.re)
      (∫ x, ‖v x‖^2 ∂μ) := by
  let b := compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
    (frameOperator_symmetric hv)
  let : Countable (Σ z, eigenspaceBasisSet (frameOperator μ v) z) :=
    orthonormal_countable b.orthonormal
  convert frameOperator_hasSum_diagonal hv b using 1
  all_goals try with_reducible_and_instances rfl
  ext i
  simp [b, compactSpectralBasis_eigen,
    inner_self_eq_norm_sq_to_K, (compactSpectralBasis _ _ _).orthonormal.1 i]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_L2MeasureInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb

section
variable {Y : Type*} [MeasurableSpace Y]

lemma l2_norm_sq (ν : Measure Y) (u : Lp ℂ 2 ν) :
    ‖u‖^2 = ∫ y, ‖u y‖^2 ∂ν := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re (L2.integrable_inner u u)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

end

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FrameDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def frameDensity {μ : Measure X} {ν : Measure Y}
    {v : X → Lp ℂ 2 ν} (hv : MemLp v 2 μ) (y : Y) : ℝ :=
  ∑' i : Σ z, eigenspaceBasisSet (frameOperator μ v) z,
    i.1.re * ‖compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
      (frameOperator_symmetric hv) i y‖^2

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketWindowed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
noncomputable def packetWindowed (g h : 𝓢(Space,ℂ)) (y : Space) : 𝓢(Space,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ
    ((SchwartzMap.compSubConstCLM ℂ y g).postcompCLM Complex.conjCLE.toContinuousLinearMap) h
lemma packetWindowed_apply (g h : 𝓢(Space,ℂ)) (y x : Space) :
    packetWindowed g h y x = conj (g (x-y))*h x := by
  unfold packetWindowed
  rw [SchwartzMap.smulLeftCLM_apply_apply
    ((SchwartzMap.compSubConstCLM ℂ y g).postcompCLM Complex.conjCLE.toContinuousLinearMap).hasTemperateGrowth]
  rfl
noncomputable def packetAnalysis (g h : 𝓢(Space,ℂ)) (y p : Space) : ℂ :=
  𝓕 (packetWindowed g h y) p
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
noncomputable def packetState (g : 𝓢(Space,ℂ)) (y p : Space) : 𝓢(Space,ℂ) :=
  𝓕⁻ (SchwartzMap.compSubConstCLM ℂ p (𝓕 (SchwartzMap.compSubConstCLM ℂ y g)))
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_ComplexWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
namespace Coulomb
noncomputable def complexWindow (g : 𝓢(Space,ℝ)) : 𝓢(Space,ℂ) :=
  g.postcompCLM Complex.ofRealCLM
@[simp] lemma complexWindow_apply (g : 𝓢(Space,ℝ)) (x : Space) :
    complexWindow g x = (g x : ℂ) := rfl

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PhaseRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
namespace Coulomb

lemma volume_real_ball_three (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure Space).real (ball 0 r) = 4*Real.pi/3*r^3 := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity)]
  ring

noncomputable def phaseRegion (R : Space → ℝ) : Set (Space × Space) :=
  {yp | ‖yp.2‖ < R yp.1}
noncomputable def phaseMeasure (R : Space → ℝ) : Measure (Space × Space) :=
  (volume.prod volume).restrict (phaseRegion R)
lemma phaseRegion_measurable {R : Space → ℝ} (hR : Measurable R) :
    MeasurableSet (phaseRegion R) := by
  exact measurableSet_lt measurable_snd.norm (hR.comp measurable_fst)

lemma phaseMeasure_lintegral {R : Space → ℝ} (hR : Measurable R)
    (f : Space × Space → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ yp, f yp ∂phaseMeasure R) = ∫⁻ y : Space, ∫⁻ p in ball 0 (R y), f (y,p) := by
  rw [phaseMeasure, ← lintegral_indicator (phaseRegion_measurable hR),
    lintegral_prod _ (hf.indicator (phaseRegion_measurable hR)).aemeasurable]
  apply lintegral_congr
  intro y
  rw [← lintegral_indicator measurableSet_ball]
  apply lintegral_congr
  intro p
  by_cases hnorm : ‖p‖ < R y <;> simp [phaseRegion, Set.indicator, hnorm]

noncomputable def fermiRadius (ρ : Space → ℝ) (y : Space) : ℝ :=
  (3/(8*Real.pi)*ρ y) ^ (1/3 : ℝ)
lemma fermiRadius_nonneg (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (y : Space) :
    0 ≤ fermiRadius ρ y := Real.rpow_nonneg (mul_nonneg (by positivity) (hρ y)) _
lemma fermiRadius_cube (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (y : Space) :
    fermiRadius ρ y ^ 3 = 3/(8*Real.pi)*ρ y := by
  rw [fermiRadius, ← Real.rpow_mul_natCast (mul_nonneg (by positivity) (hρ y))]
  norm_num
lemma fermiRadius_measurable (ρ : Space → ℝ) (hρ : Measurable ρ) :
    Measurable (fermiRadius ρ) := by
  unfold fermiRadius
  fun_prop
lemma fermiRadius_ball_mass (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (y : Space) :
    (volume : Measure Space) (ball 0 (fermiRadius ρ y)) = ENNReal.ofReal (ρ y/2) := by
  rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow (fermiRadius_nonneg ρ hρ y),
    ← ENNReal.ofReal_mul (pow_nonneg (fermiRadius_nonneg ρ hρ y) _), fermiRadius_cube ρ hρ y]
  congr 1
  field_simp
  ring

lemma fermiMeasure_mass (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (hI : Integrable ρ) :
    phaseMeasure (fermiRadius ρ) univ = ENNReal.ofReal ((∫ y : Space, ρ y)/2) := by
  rw [← lintegral_one, phaseMeasure_lintegral (fermiRadius_measurable ρ hm) _ measurable_const]
  simp only [lintegral_one, Measure.restrict_apply_univ, fermiRadius_ball_mass ρ hρ]
  rw [← ofReal_integral_eq_lintegral_ofReal (hI.div_const 2)
    (Filter.Eventually.of_forall (fun y => div_nonneg (hρ y) (by norm_num))), integral_div]

lemma fermiMeasure_finite (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (hI : Integrable ρ) : IsFiniteMeasure (phaseMeasure (fermiRadius ρ)) := by
  constructor
  rw [fermiMeasure_mass ρ hρ hm hI]
  exact ENNReal.ofReal_lt_top

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_ThomasFermiKineticConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
namespace Coulomb
lemma fermiMeasure_center_lintegral (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (f : Space → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ yp, f yp.1 ∂phaseMeasure (fermiRadius ρ)) =
      ∫⁻ y : Space, f y * ENNReal.ofReal (ρ y/2) := by
  rw [phaseMeasure_lintegral (fermiRadius_measurable ρ hm) (fun yp : Space × Space => f yp.1) (hf.comp measurable_fst)]
  simp only [lintegral_const, Measure.restrict_apply_univ, fermiRadius_ball_mass ρ hρ]

lemma fermiMeasure_center_integral (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (f : Space → ℝ) (hf : Measurable f) (hfp : ∀ y, 0 ≤ f y) :
    (∫ yp, f yp.1 ∂phaseMeasure (fermiRadius ρ)) = (1/2:ℝ)*∫ y : Space, f y*ρ y := by
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun yp : Space × Space => f yp.1) (Filter.Eventually.of_forall (fun yp : Space × Space => hfp yp.1))
    (hf.comp measurable_fst).aestronglyMeasurable, fermiMeasure_center_lintegral ρ hρ hm _ hf.ennreal_ofReal]
  have he (y : Space) : ENNReal.ofReal (f y) * ENNReal.ofReal (ρ y/2) =
      ENNReal.ofReal ((1/2:ℝ)*(f y*ρ y)) := by
    rw [← ENNReal.ofReal_mul (hfp y)]
    congr 1
    ring
  simp only [he]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun y => mul_nonneg (by norm_num) (mul_nonneg (hfp y) (hρ y))))
    ((hf.mul hm).const_mul (1/2:ℝ)).aestronglyMeasurable, integral_const_mul]

noncomputable def thomasFermiKineticConstant : ℝ := (3/10:ℝ)*(3*Real.pi^2)^(2/3:ℝ)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
namespace Coulomb

def packetDensity (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) (x : Space) : ℝ :=
  ∫ y : Space, g (x-y)^2*ρ y

lemma schwartz_square_le (g : 𝓢(Space,ℝ)) (x : Space) :
    g x^2 ≤ (SchwartzMap.seminorm ℝ 0 0 g)^2 := by
  have h := g.norm_le_seminorm ℝ x
  simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg (g x)) h 2

end Coulomb

open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CoreScreenedField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
namespace Coulomb

def coreScreenedField {M m : ℕ} (S : Nuclei M) (u : H1Vector m) (x : Space) : ℝ :=
  attraction S x - coreCoulombPotential u x

end Coulomb

open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_UniformBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

def uniformBall (a M : ℝ) (x : Space) : ℝ :=
  (Metric.ball (0 : Space) a).indicator (fun _ => M / (4*Real.pi/3*a^3)) x

def ballCloud (y : Space) (a M : ℝ) (x : Space) : ℝ := uniformBall a M (x-y)

lemma uniformBall_nonneg {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (x : Space) :
    0 ≤ uniformBall a M x := by
  apply Set.indicator_nonneg
  intro x hx
  exact div_nonneg hM (by positivity)

lemma uniformBall_le {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (x : Space) :
    uniformBall a M x ≤ M/(4*Real.pi/3*a^3) := by
  exact Set.indicator_le_self' (fun _ _ => div_nonneg hM (by positivity)) _

lemma uniformBall_measurable (a M : ℝ) : Measurable (uniformBall a M) :=
  measurable_const.indicator measurableSet_ball

lemma uniformBall_integrable (a M : ℝ) : Integrable (uniformBall a M) := by
  exact (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const (C := M/(4*Real.pi/3*a^3)) measure_ball_lt_top.ne)

lemma uniformBall_mass {a : ℝ} (ha : 0 < a) (M : ℝ) :
    (∫ x, uniformBall a M x) = M := by
  unfold uniformBall
  rw [integral_indicator measurableSet_ball, integral_const]
  rw [measureReal_restrict_apply_univ, smul_eq_mul, volume_real_ball_three a ha.le]
  field_simp [ha.ne', Real.pi_ne_zero]

lemma uniformBall_power {a : ℝ} (ha : 0 < a) (M : ℝ) :
    (∫ x, uniformBall a M x^(5/3:ℝ)) = (4*Real.pi/3*a^3)*(M/(4*Real.pi/3*a^3))^(5/3:ℝ) := by
  have he : (fun x => uniformBall a M x^(5/3:ℝ)) =
      (Metric.ball (0:Space) a).indicator (fun _ => (M/(4*Real.pi/3*a^3))^(5/3:ℝ)) := by
    funext x
    simp only [uniformBall,Set.indicator_apply]
    split <;> simp
  rw [he, integral_indicator measurableSet_ball, integral_const]
  rw [measureReal_restrict_apply_univ, smul_eq_mul, volume_real_ball_three a ha.le]

lemma uniformBall_radial (a M : ℝ) (x : Space) :
    uniformBall a M x = uniformBall a M (EuclideanSpace.single 0 ‖x‖) := by
  simp only [uniformBall,Set.indicator_apply,Metric.mem_ball,dist_zero_right,
    PiLp.norm_single,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg x)]

lemma uniformBall_support (a M : ℝ) (x : Space) (hx : a < ‖x‖) :
    uniformBall a M x = 0 := by
  apply Set.indicator_of_notMem
  simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx.le

lemma ballCloud_mass {a : ℝ} (ha : 0 < a) (M : ℝ) (y : Space) :
    (∫ x, ballCloud y a M x) = M := by
  unfold ballCloud
  rw [integral_sub_right_eq_self, uniformBall_mass ha]

lemma ballCloud_integrable (a M : ℝ) (y : Space) : Integrable (ballCloud y a M) :=
  (uniformBall_integrable a M).comp_sub_right y

lemma ballCloud_measurable (a M : ℝ) (y : Space) : Measurable (ballCloud y a M) :=
  (uniformBall_measurable a M).comp (by fun_prop)

lemma ballCloud_coulomb {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y x : Space)
    (hxy : a ≤ ‖x-y‖) :
    (∫ z, coulombKernel (x-z)*ballCloud y a M z) = M*coulombKernel (x-y) := by
  have he : (∫ z, coulombKernel (x-z)*ballCloud y a M z) =
      ∫ z, coulombKernel ((x-y)-z)*uniformBall a M z := by
    rw [← integral_sub_right_eq_self (fun z => coulombKernel ((x-y)-z)*uniformBall a M z) y]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      change coulombKernel (x-z)*uniformBall a M (z-y) = _
      have hz : (x-y)-(z-y) = x-z := by abel
      dsimp only
      rw [hz])
  rw [he,radial_coulomb_integral_eq (uniformBall_integrable a M) (uniformBall_measurable a M)
    (uniformBall_nonneg ha hM) (uniformBall_le ha hM) (uniformBall_radial a M) ha.le
    (uniformBall_support a M) (by intro hh; simp [hh] at hxy; linarith) hxy,
    uniformBall_mass ha, mul_comm]

lemma ballCloud_coulomb_bound {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y x : Space) :
    (∫ z, coulombKernel (x-z)*ballCloud y a M z) ≤ (5/2:ℝ)*M/a := by
  have H := coulomb_convolution_bound (ballCloud_integrable a M y) (ballCloud_measurable a M y)
    (fun z => uniformBall_nonneg ha hM (z-y)) (fun z => uniformBall_le ha hM (z-y)) ha x
  rw [ballCloud_mass ha] at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [ha.ne', Real.pi_ne_zero]
  ring

lemma ballCloud_coulombBilinear_bound {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y : Space) :
    coulombBilinear (ballCloud y a M) (ballCloud y a M) ≤ (5/2:ℝ)*M^2/a := by
  have hi := ballCloud_integrable a M y
  have hm := ballCloud_measurable a M y
  have hb (z : Space) : ‖ballCloud y a M z‖ ≤ M/(4*Real.pi/3*a^3) := by
    change ‖uniformBall a M (z-y)‖ ≤ _
    rw [Real.norm_of_nonneg (uniformBall_nonneg ha hM (z-y))]
    exact uniformBall_le ha hM _
  rw [coulombBilinear_iterated hi hm hi hm hb]
  have hip : Integrable (fun z => ballCloud y a M z *
      (∫ w, coulombKernel (z-w)*ballCloud y a M w)) := by
    apply ((coulomb_pair_integrable hi hm hi hm hb).integral_prod_left).congr
    exact Eventually.of_forall (fun z => by
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun w => by ring))
  have H := integral_mono hip (hi.mul_const ((5/2:ℝ)*M/a)) (fun z =>
    mul_le_mul_of_nonneg_left (ballCloud_coulomb_bound ha hM y z) (uniformBall_nonneg ha hM (z-y)))
  rw [integral_mul_const,ballCloud_mass ha] at H
  calc
    _ ≤ M*((5/2:ℝ)*M/a) := H
    _ = (5/2:ℝ)*M^2/a := by ring

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma coreCoulombPotential_ballCloud {k : ℕ} (u : H1Vector k)
    {A : Set Space} (hu : SpatiallySupported u A)
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y : Space)
    (hsep : ∀ z ∈ A, a ≤ ‖z-y‖) :
    (∫ z, coreCoulombPotential u z*ballCloud y a M z) = M*coreCoulombPotential u y := by
  rw [coreCoulombPotential_fubini u _ (ballCloud_integrable a M y)]
  simp only [coreCoulombPotential,Finset.mul_sum,← integral_const_mul]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [hu s] with x hx
  by_cases he : u.value s x = 0
  · simp [he]
  · have hz : position x i ∈ A := (by_contra (fun hn => he (hx hn)) : x ∈ allPositions A) i
    rw [ballCloud_coulomb ha hM y (position x i) (hsep _ hz)]
    ring

lemma attraction_ballCloud {J : ℕ} (S : Nuclei J)
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y : Space)
    (hsep : ∀ j, a ≤ ‖S.position j-y‖) :
    (∫ z, attraction S z*ballCloud y a M z) = M*attraction S y := by
  have hi j : Integrable (fun z => S.charge j*(coulombKernel (S.position j-z)*ballCloud y a M z)) :=
    (coulomb_convolution_integrable (ballCloud_integrable a M y) (ballCloud_measurable a M y)
      (fun z => uniformBall_nonneg ha hM (z-y)) (fun z => uniformBall_le ha hM (z-y)) ha (S.position j)).const_mul _
  simp only [attraction,Finset.sum_mul,Finset.mul_sum]
  simp_rw [coulombKernel_sub_comm _ (S.position _), mul_assoc]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, ballCloud_coulomb ha hM y (S.position j) (hsep j)]
  ring

lemma coreScreenedField_ballCloud {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {A : Set Space} (hu : SpatiallySupported u A)
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y : Space)
    (hcore : ∀ z ∈ A, a ≤ ‖z-y‖) (hnuc : ∀ j, a ≤ ‖S.position j-y‖) :
    (∫ z, coreScreenedField S u z*ballCloud y a M z) = M*coreScreenedField S u y := by
  have hi := ballCloud_integrable a M y
  have hn : Integrable (fun z => attraction S z*ballCloud y a M z) := by
    simp only [attraction,Finset.sum_mul]
    apply integrable_finsetSum
    intro j _
    have H := (coulomb_convolution_integrable hi (ballCloud_measurable a M y)
      (fun z => uniformBall_nonneg ha hM (z-y)) (fun z => uniformBall_le ha hM (z-y)) ha (S.position j)).const_mul (S.charge j)
    apply H.congr
    exact Eventually.of_forall (fun z => by dsimp only; rw [coulombKernel_sub_comm]; ring)
  simp only [coreScreenedField,sub_mul]
  rw [integral_sub hn (coreCoulombPotential_mul_integrable u _ hi),attraction_ballCloud S ha hM y hnuc,
    coreCoulombPotential_ballCloud u hu ha hM y hcore]
  ring

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RestrictedField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def restrictedOutPotential {m : ℕ} (x : Configuration m) (A : Set Space) (y : Space) : ℝ :=
  ∑ i : Fin m, if position x i ∈ A then coulombKernel (position x i-y) else 0

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_CutCombinatorics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open scoped BigOperators Classical
namespace Coulomb

lemma sum_product_labels {I L : Type*} [Fintype I] [Fintype L] [DecidableEq I]
    (f : I → L → ℝ) : (∑ p : I → L, ∏ i, f i (p i)) = ∏ i, ∑ l, f i l := by
  simpa only [Fintype.piFinset_univ] using
    (Finset.prod_univ_sum (fun _ : I => (Finset.univ : Finset L)) f).symm

lemma product_partition_square {I L : Type*} [Fintype I] [Fintype L] [DecidableEq I]
    (f : I → L → ℝ) (hf : ∀ i, ∑ l, f i l ^ 2 = 1) :
    ∑ p : I → L, (∏ i, f i (p i))^2 = 1 := by
  simp_rw [←Finset.prod_pow]
  rw [sum_product_labels (fun i l => f i l ^ 2)]
  simp only [hf,Finset.prod_const_one]

lemma sum_slot_product {I L : Type*} [Fintype I] [Fintype L] [DecidableEq I]
    (f : I → L → ℝ) (g : L → ℝ) (i : I)
    (hf : ∀ j, ∑ l, f j l = 1) :
    (∑ p : I → L, g (p i) * ∏ j ∈ Finset.univ.erase i, f j (p j)) = ∑ l, g l := by
  let w : I → L → ℝ := fun j l => if j=i then g l else f j l
  have hp (p : I → L) : g (p i) * ∏ j ∈ Finset.univ.erase i, f j (p j) = ∏ j, w j (p j) := by
    rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [w,ite_eq_left rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact (ite_eq_right (Finset.ne_of_mem_erase hj)).symm
  simp_rw [hp]
  rw [sum_product_labels w]
  rw [Finset.prod_eq_single i]
  · simp [w]
  · intro j hj hji
    simp only [w,ite_eq_right hji,hf]
  · simp

lemma sum_slot_product_square {I L : Type*} [Fintype I] [Fintype L] [DecidableEq I]
    (f : I → L → ℝ) (g : L → ℝ) (i : I)
    (hf : ∀ j, ∑ l, f j l ^ 2 = 1) :
    (∑ p : I → L, (g (p i) * ∏ j ∈ Finset.univ.erase i, f j (p j))^2) = ∑ l, g l ^ 2 := by
  simp_rw [mul_pow,←Finset.prod_pow]
  exact sum_slot_product (fun i l => f i l ^ 2) (fun l => g l ^ 2) i hf

lemma abs_partition_le_one {L : Type*} [Fintype L] (f : L → ℝ)
    (hf : ∑ l, f l ^ 2 = 1) (l : L) : |f l| ≤ 1 := by
  have h := Finset.single_le_sum (fun j _ => sq_nonneg (f j)) (Finset.mem_univ l)
  rw [hf] at h
  nlinarith [sq_abs (f l),abs_nonneg (f l)]

lemma abs_prod_le_one {I : Type*} (s : Finset I) (f : I → ℝ)
    (h : ∀ i ∈ s, |f i| ≤ 1) : |∏ i ∈ s, f i| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) h
end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def tensorCut {n : ℕ} {L : Type*} (χ : L → Space → ℝ) (p : Fin n → L) (x : Configuration n) : ℝ :=
  ∏ i, χ (p i) (position x i)

lemma tensorCut_contDiff {n : ℕ} {L : Type*} (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l)) (p : Fin n → L) :
    ContDiff ℝ (⊤ : ℕ∞) (tensorCut χ p) := by
  unfold tensorCut
  apply contDiff_prod
  intro i hi
  exact (hχ (p i)).comp (positionCLM i).contDiff

lemma tensorCut_fderiv {n : ℕ} {L : Type*} (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l)) (p : Fin n → L)
    (x : Configuration n) (i : Fin n) (b : Fin 3) :
    fderiv ℝ (tensorCut χ p) x (EuclideanSpace.single (i,b) 1) =
      fderiv ℝ (χ (p i)) (position x i) (EuclideanSpace.single b 1) *
        ∏ j ∈ Finset.univ.erase i, χ (p j) (position x j) := by
  have hd (j : Fin n) : DifferentiableAt ℝ (fun y : Configuration n => χ (p j) (position y j)) x := by
    exact ((hχ (p j)).differentiable (by simp) (positionCLM j x)).comp x
      (positionCLM j).differentiableAt
  have he (j : Fin n) : fderiv ℝ (fun y : Configuration n => χ (p j) (position y j)) x =
      (fderiv ℝ (χ (p j)) (position x j)).comp (positionCLM j) := by
    exact (((hχ (p j)).differentiable (by simp) (position x j)).hasFDerivAt.comp x
      (positionCLM j).hasFDerivAt).fderiv
  unfold tensorCut
  rw [fderiv_finsetProd (fun j _ => hd j),sum_apply]
  simp only [smul_apply,smul_eq_mul,he,ContinuousLinearMap.comp_apply,positionCLM_single]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    ring
  · intro j hj hji
    simp only [ite_eq_right hji,map_zero,mul_zero]
  · simp

lemma tensorCut_partition {n : ℕ} {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) (x : Configuration n) :
    ∑ p : Fin n → L, tensorCut χ p x ^ 2 = 1 :=
  product_partition_square (fun i l => χ l (position x i)) (fun i => hp (position x i))

lemma tensorCut_abs_le_one {n : ℕ} {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) (p : Fin n → L) (x : Configuration n) :
    |tensorCut χ p x| ≤ 1 :=
  abs_prod_le_one _ _ (fun i _ => abs_partition_le_one (fun l => χ l (position x i)) (hp _) _)

lemma tensorCut_partial_bound {n : ℕ} {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) {D : ℝ} (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin n → L) (a : Fin n × Fin 3) (x : Configuration n) :
    |fderiv ℝ (tensorCut χ p) x (EuclideanSpace.single a 1)| ≤ D := by
  rcases a with ⟨i,b⟩
  rw [tensorCut_fderiv χ hχ,abs_mul]
  calc
    _ ≤ D*1 := mul_le_mul (hd _ _ _) (abs_prod_le_one _ _
      (fun j _ => abs_partition_le_one (fun l => χ l (position x j)) (hp _) _)) (abs_nonneg _) hD
    _ = D := mul_one D

lemma tensorCut_gradient_square_sum {n : ℕ} {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) (x : Configuration n) (i : Fin n) (b : Fin 3) :
    (∑ p : Fin n → L, (fderiv ℝ (tensorCut χ p) x (EuclideanSpace.single (i,b) 1))^2) =
      ∑ l, (fderiv ℝ (χ l) (position x i) (EuclideanSpace.single b 1))^2 := by
  simp_rw [tensorCut_fderiv χ hχ]
  exact sum_slot_product_square (fun j l => χ l (position x j))
    (fun l => fderiv ℝ (χ l) (position x i) (EuclideanSpace.single b 1)) i (fun j => hp _)

def H1Vector.labelCut {n : ℕ} {L : Type*} [Fintype L] (ψ : H1Vector n)
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin n → L) : H1Vector n :=
  ψ.smoothMul (tensorCut χ p) (tensorCut_contDiff χ hχ p) 1 D
    (tensorCut_abs_le_one χ hp p) (tensorCut_partial_bound χ hχ hp hD hd p)

lemma form_labelCut {J n : ℕ} {L : Type*} [Fintype L] (S : Nuclei J) (ψ : H1Vector n)
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D) :
    (∑ p : Fin n → L, form S (ψ.labelCut χ hχ hp D hD hd p)) =
      form S ψ+(1/2:ℝ)*∑ s, ∑ a : Fin n × Fin 3, ∫ x,
        (∑ l, (fderiv ℝ (χ l) (position x a.1) (EuclideanSpace.single a.2 1))^2)*‖ψ.value s x‖^2 := by
  unfold H1Vector.labelCut
  rw [form_smooth_partition S ψ _ _ _ _ _ _ (tensorCut_partition χ hp)]
  simp_rw [tensorCut_gradient_square_sum χ hχ hp]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_NuclearPotentialSplitJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

lemma H1Vector.core_nuclear_integrable {M m k : ℕ} (ψ : H1Vector (m+k))
    (S : Nuclei M) (st : Spins (m+k)) :
    Integrable (fun z => nuclearPotential S ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2) := by
  simp only [nuclearPotential, attraction, position_split_right, Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have H := (ψ.nuclear_coulomb_integrable_bound st (Fin.natAdd m i) (S.position j)
    (by norm_num : (0:ℝ)<1)).1
  simpa only [mul_assoc] using H.const_mul (S.charge j)

lemma H1Vector.core_pair_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (st : Spins (m+k)) :
    Integrable (fun z => pairPotential ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2) := by
  simp only [pairPotential, position_split_right, Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  by_cases hij : i < j
  · simp only [ite_eq_left hij]
    exact (ψ.pair_coulomb_integrable_bound st (Fin.natAdd m i) (Fin.natAdd m j)
      (fun he => hij.ne (by apply Fin.ext; have hh := congrArg Fin.val he; simpa only [Fin.val_natAdd, Nat.add_left_cancel_iff] using hh)) (by norm_num : (0:ℝ)<1)).1
  · simp only [ite_eq_right hij, zero_mul]
    exact integrable_zero _ _ _

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_CoreKinetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

lemma potentialForm_coreSlice_parameter_ae {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    (V : Configuration m → Configuration k → ℝ) :
    (fun x => potentialForm (V x) (ψ.coreSlice s x)) =ᵐ[volume]
      fun x => ∑ t : Spins k, ∫ y, V x y * ‖ψ.value (Fin.append s t) (joinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.coreSliceRegular_ae s] with x hx
  simp only [potentialForm, ψ.coreSlice_value s hx]

lemma potentialForm_coreSlice_parameter_integrable {m k : ℕ} (ψ : H1Vector (m+k))
    (s : Spins m) (V : Configuration m → Configuration k → ℝ)
    (hV : ∀ t : Spins k, Integrable (fun z =>
      V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 *
        ‖ψ.value (Fin.append s t) z‖^2)) :
    Integrable (fun x => potentialForm (V x) (ψ.coreSlice s x)) := by
  apply Integrable.congr _ (potentialForm_coreSlice_parameter_ae ψ s V).symm
  apply integrable_finsetSum
  intro t _
  have H := ((joinConfiguration_measurePreserving m k).integrable_comp_emb
    (joinConfiguration m k).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr (hV t)
  change Integrable (fun z : Configuration m × Configuration k =>
    V ((joinConfiguration m k).symm (joinConfiguration m k z)).1
      ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
        ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) at H
  simp only [ContinuousLinearEquiv.symm_apply_apply] at H
  exact H.integral_prod_left

lemma integral_potentialForm_coreSlice_parameter {m k : ℕ} (ψ : H1Vector (m+k))
    (V : Configuration m → Configuration k → ℝ)
    (hV : ∀ st : Spins (m+k), Integrable (fun z =>
      V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2)) :
    (∑ s : Spins m, ∫ x, potentialForm (V x) (ψ.coreSlice s x)) =
      ∑ st : Spins (m+k), ∫ z,
        V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2 := by
  have hs (s : Spins m) : (∫ x, potentialForm (V x) (ψ.coreSlice s x)) =
      ∑ t : Spins k, ∫ z,
        V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 *
          ‖ψ.value (Fin.append s t) z‖^2 := by
    rw [integral_congr_ae (potentialForm_coreSlice_parameter_ae ψ s V)]
    have hi (t : Spins k) : Integrable (fun z : Configuration m × Configuration k =>
        V z.1 z.2 * ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) := by
      have H := ((joinConfiguration_measurePreserving m k).integrable_comp_emb
        (joinConfiguration m k).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr
        (hV (Fin.append s t))
      change Integrable (fun z : Configuration m × Configuration k =>
        V ((joinConfiguration m k).symm (joinConfiguration m k z)).1
          ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
          ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) at H
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
    rw [integral_finsetSum _ (fun t _ => (hi t).integral_prod_left)]
    apply Finset.sum_congr rfl
    intro t _
    rw [← integral_prod _ (hi t)]
    have H := (joinConfiguration_measurePreserving m k).integral_comp'
      (fun z => V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 *
        ‖ψ.value (Fin.append s t) z‖^2)
    change (∫ z : Configuration m × Configuration k,
        V ((joinConfiguration m k).symm (joinConfiguration m k z)).1
          ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
          ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2 ∂volume.prod volume) = _ at H
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
  simp_rw [hs]
  rw [← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
    ∫ z, V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 *
      ‖ψ.value (Fin.append st.1 st.2) z‖^2)]
  exact Fintype.sum_equiv (Fin.appendEquiv m k) _ _ (fun _ => rfl)

noncomputable def outerKinetic {m k : ℕ} (ψ : H1Vector (m+k)) : ℝ :=
  (1/2 : ℝ) * ∑ st : Spins (m+k), ∑ a : Fin m × Fin 3,
    ∫ z, ‖ψ.gradient st (Fin.castAdd k a.1,a.2) z‖^2

lemma form_normalized_weight {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) :
    mass ψ * form S ψ.normalized = form S ψ := by
  change mass ψ * (kinetic ψ.normalized - potentialForm (nuclearPotential S) ψ.normalized +
    potentialForm pairPotential ψ.normalized) = _
  rw [mul_add, mul_sub, kinetic_normalized_weight, potentialForm_normalized_weight,
    potentialForm_normalized_weight]
  rfl

lemma form_coreSlice_integrable {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k)) (s : Spins m) :
    Integrable (fun x => form S (ψ.coreSlice s x)) :=
  ((kinetic_coreSlice_integrable ψ s).sub
    (potentialForm_coreSlice_integrable ψ s (nuclearPotential S)
      (fun t => ψ.core_nuclear_integrable S (Fin.append s t)))).add
        (potentialForm_coreSlice_integrable ψ s pairPotential
          (fun t => ψ.core_pair_integrable (Fin.append s t)))

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SliceExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma nuclearEnergy_unit_eq_coreCoulomb {k : ℕ} (u : H1Vector k) (a : Space) :
    nuclearEnergy (unitNucleus a) u = coreCoulombPotential u a := by
  unfold nuclearEnergy coreCoulombPotential
  apply Finset.sum_congr rfl
  intro s _
  simp only [attraction_unitNucleus, Finset.sum_mul]
  exact integral_finsetSum _ (fun i _ =>
    (u.nuclear_coulomb_integrable_bound s i a (by norm_num : (0:ℝ)<1)).1)

def sliceExpectation {m k : ℕ} (ψ : H1Vector (m+k)) (f : Spins m → Configuration m → ℝ) : ℝ :=
  ∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x)*f s x

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_DeletedLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma normalized_coreForm_weight_integrable {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*form S (ψ.coreSlice s x).normalized) := by
  simp only [form_normalized_weight]
  exact form_coreSlice_integrable S ψ s

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_NearCoulombFiveHalves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma density_memLp_fiveThirds (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (ht : Integrable (fun x => ρ x^(5/3:ℝ))) : MemLp ρ (5/3:ℝ≥0∞) := by
  apply (integrable_norm_rpow_iff hm.aestronglyMeasurable (by norm_num : (5/3:ℝ≥0∞) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num) : (5/3:ℝ≥0∞) ≠ ⊤)).mp
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat,Real.norm_of_nonneg (hp _)] using ht

lemma compact_density_integrable (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (ht : Integrable (fun x => ρ x^(5/3:ℝ))) (K : Set Space) (hK : IsCompact K)
    (hs : ∀ x, x ∉ K → ρ x = 0) : Integrable ρ := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hLp : MemLp ρ (5/3:ℝ≥0∞) (volume.restrict K) :=
    (density_memLp_fiveThirds ρ hp hm ht).mono_measure Measure.restrict_le_self
  have hI := hLp.integrable (by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num : (1:ℝ≥0∞) ≤ 5/3)
  exact IntegrableOn.integrable_of_forall_notMem_eq_zero hI hs

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_SchwartzSquareIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma schwartz_square_integrable (g : 𝓢(Space,ℝ)) : Integrable (fun x : Space => g x^2) := by
  exact (g.memLp 2 volume).integrable_sq

lemma window_shift_integrable (g : 𝓢(Space,ℝ)) (a : Space) :
    Integrable (fun x : Space => g (x-a)^2) := (schwartz_square_integrable g).comp_sub_right a

lemma window_shift_coulomb_integral (g : 𝓢(Space,ℝ)) (a x : Space) :
    (∫ y, coulombKernel (x-y)*g (y-a)^2) = ∫ y, coulombKernel ((x-a)-y)*g y^2 := by
  rw [← integral_sub_right_eq_self (fun y => coulombKernel ((x-a)-y)*g y^2) a]
  congr 1
  funext y
  congr 2
  abel

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_WindowCoulomb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma window_coulomb_eq (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖)) {R : ℝ} (hR : 0 < R)
    (hs : ∀ y, R < ‖y‖ → g y = 0) {x : Space} (hx : R ≤ ‖x‖) :
    (∫ y, coulombKernel (x-y)*g y^2) = coulombKernel x := by
  have hx0 : x ≠ 0 := by intro he; subst x; simp at hx; linarith
  simpa only [hg,mul_one] using radial_coulomb_integral_eq (schwartz_square_integrable g)
    (g.continuous.measurable.pow_const 2) (fun x => sq_nonneg (g x)) (schwartz_square_le g)
    (fun y => congrArg (fun t : ℝ => t^2) (hrad y)) hR.le (fun y hy => by simp [hs y hy]) hx0 hx

lemma window_coulomb_bound (g : 𝓢(Space,ℝ)) (x : Space) :
    (∫ y, coulombKernel (x-y)*g y^2) ≤
      2*Real.pi*(SchwartzMap.seminorm ℝ 0 0 g)^2 + ∫ y : Space, g y^2 := by
  simpa only [one_pow,mul_one,one_div,one_mul,inv_one] using
    coulomb_convolution_bound (schwartz_square_integrable g) (g.continuous.measurable.pow_const 2)
      (fun y => sq_nonneg (g y)) (schwartz_square_le g) (by norm_num : (0:ℝ)<1) x

lemma packetDensity_coulomb_prod_integrable (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ) (a : Space) :
    Integrable (fun p : Space × Space => coulombKernel (a-p.1)*g (p.1-p.2)^2*ρ p.2)
      (volume.prod volume) := by
  let C := 2*Real.pi*(SchwartzMap.seminorm ℝ 0 0 g)^2+∫ y : Space, g y^2
  have hF : Measurable (fun p : Space × Space => coulombKernel (a-p.1)*g (p.1-p.2)^2*ρ p.2) :=
    ((coulombKernel_measurable.comp (measurable_const.sub measurable_fst)).mul
      ((g.continuous.measurable.comp (measurable_fst.sub measurable_snd)).pow_const 2)).mul
        (hm.comp measurable_snd)
  have hI (y : Space) : Integrable (fun x => coulombKernel (a-x)*g (x-y)^2) :=
    coulomb_convolution_integrable (window_shift_integrable g y)
      (((g.continuous.measurable.comp (measurable_id.sub measurable_const)).pow_const 2))
      (fun x => sq_nonneg _) (fun x => schwartz_square_le g (x-y)) (by norm_num : (0:ℝ)<1) a
  apply (integrable_prod_iff' hF.aestronglyMeasurable).2
  constructor
  · exact Eventually.of_forall fun y => (hI y).mul_const (ρ y)
  · apply (hi.const_mul C).mono' hF.aestronglyMeasurable.prod_swap.norm.integral_prod_right'
    exact Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      have he : (∫ x, ‖coulombKernel (a-x)*g (x-y)^2*ρ y‖) =
          (∫ x, coulombKernel (a-x)*g (x-y)^2)*ρ y := by
        rw [←integral_mul_const]
        exact integral_congr_ae (Eventually.of_forall fun _ =>
          Real.norm_of_nonneg (mul_nonneg (mul_nonneg (coulombKernel_nonneg _) (sq_nonneg _)) (hp y)))
      change (∫ x, ‖coulombKernel (a-x)*g (x-y)^2*ρ y‖) ≤ C*ρ y
      rw [he,window_shift_coulomb_integral]
      exact mul_le_mul_of_nonneg_right (window_coulomb_bound g _) (hp y)

lemma packetDensity_coulomb_integral (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ) (a : Space) :
    (∫ x, coulombKernel (a-x)*packetDensity g ρ x) =
      ∫ y, (∫ x, coulombKernel ((a-y)-x)*g x^2)*ρ y := by
  have hI := packetDensity_coulomb_prod_integrable g ρ hp hm hi a
  calc
    _ = ∫ x, ∫ y, coulombKernel (a-x)*g (x-y)^2*ρ y := by
      unfold packetDensity
      simp_rw [←integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => integral_congr_ae (Eventually.of_forall fun y => by ring))
    _ = ∫ y, ∫ x, coulombKernel (a-x)*g (x-y)^2*ρ y := integral_integral_swap hI
    _ = _ := by simp_rw [integral_mul_const, window_shift_coulomb_integral]

lemma packetDensity_coulomb_eq (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖)) {R : ℝ} (hR : 0 < R)
    (hs : ∀ y, R < ‖y‖ → g y = 0) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ) (a : Space)
    (hsep : ∀ y, ρ y ≠ 0 → R ≤ ‖a-y‖) :
    (∫ x, coulombKernel (a-x)*packetDensity g ρ x) = ∫ y, coulombKernel (a-y)*ρ y := by
  rw [packetDensity_coulomb_integral g ρ hp hm hi a]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    by_cases hy : ρ y = 0
    · simp [hy]
    · change (∫ x, coulombKernel (a-y-x)*g x^2)*ρ y = coulombKernel (a-y)*ρ y
      rw [window_coulomb_eq g hg hrad hR hs (hsep y hy)]

lemma separated_density_coulomb_integrable {ρ : Space → ℝ} (hp : ∀ y, 0 ≤ ρ y)
    (hm : Measurable ρ) (hi : Integrable ρ) {R : ℝ} (hR : 0 < R) (a : Space)
    (hsep : ∀ y, ρ y ≠ 0 → R ≤ ‖a-y‖) :
    Integrable (fun y => coulombKernel (a-y)*ρ y) := by
  apply (hi.const_mul R⁻¹).mono'
  · exact ((coulombKernel_measurable.comp (measurable_const.sub measurable_id)).mul hm).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hp y))]
      by_cases hy : ρ y = 0
      · simp [hy]
      · exact mul_le_mul_of_nonneg_right (by simpa [coulombKernel,one_div] using (one_div_le_one_div_of_le hR (hsep y hy))) (hp y)

lemma attraction_packet_eq {M : ℕ} (S : Nuclei M)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖)) {R : ℝ} (hR : 0 < R)
    (hs : ∀ y, R < ‖y‖ → g y = 0) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ)
    (hsep : ∀ j y, ρ y ≠ 0 → R ≤ ‖S.position j-y‖) :
    (∫ x, attraction S x*packetDensity g ρ x) = ∫ x, attraction S x*ρ x := by
  have hn (j : Fin M) : Integrable (fun x => S.charge j*(coulombKernel (S.position j-x)*ρ x)) :=
    (separated_density_coulomb_integrable hp hm hi hR (S.position j) (hsep j)).const_mul _
  have hsmooth (j : Fin M) : Integrable (fun x => S.charge j*(coulombKernel (S.position j-x)*packetDensity g ρ x)) := by
    have h := (packetDensity_coulomb_prod_integrable g ρ hp hm hi (S.position j)).integral_prod_left
    apply (h.const_mul (S.charge j)).congr
    exact Eventually.of_forall fun x => by
      simp only [packetDensity,←integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by ring)
  simp only [attraction,Finset.sum_mul]
  simp_rw [coulombKernel_sub_comm _ (S.position _),mul_assoc]
  rw [integral_finsetSum _ (fun j _ => hsmooth j),integral_finsetSum _ (fun j _ => hn j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,integral_const_mul,
    packetDensity_coulomb_eq g hg hrad hR hs ρ hp hm hi _ (hsep j)]

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RawThomasFermiEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

def rawThomasFermiEnergy (Φ ρ : Space → ℝ) : ℝ :=
  thomasFermiCoefficient*(∫ y, ρ y^(5/3:ℝ)) - (∫ y, Φ y*ρ y) + coulombBilinear ρ ρ/2

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_BallTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
noncomputable section
namespace Coulomb

def ballKineticCoefficient : ℝ :=
  thomasFermiCoefficient*(4*Real.pi/3)/(4*Real.pi/3)^(5/3:ℝ)

lemma ballKineticCoefficient_pos : 0 < ballKineticCoefficient := by
  unfold ballKineticCoefficient thomasFermiCoefficient
  positivity

lemma ballCloud_power {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y : Space) :
    thomasFermiCoefficient*(∫ x, ballCloud y a M x^(5/3:ℝ)) =
      ballKineticCoefficient*M^(5/3:ℝ)/a^2 := by
  unfold ballCloud
  rw [integral_sub_right_eq_self (fun x => uniformBall a M x^(5/3:ℝ)) y,uniformBall_power ha]
  have hc : 0 < 4*Real.pi/3 := by positivity
  rw [Real.div_rpow hM (by positivity),Real.mul_rpow hc.le (pow_nonneg ha.le 3)]
  have he : (a^3)^(5/3:ℝ) = a^5 := by
    rw [← Real.rpow_natCast a 3, ← Real.rpow_mul ha.le]
    norm_num
  rw [he]
  unfold ballKineticCoefficient
  field_simp [ha.ne', (Real.rpow_pos_of_pos hc (5/3:ℝ)).ne']

lemma ballCloud_rawTF_bound {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {A : Set Space} (hu : SpatiallySupported u A)
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y : Space)
    (hcore : ∀ z ∈ A, a ≤ ‖z-y‖) (hnuc : ∀ j, a ≤ ‖S.position j-y‖) :
    rawThomasFermiEnergy (coreScreenedField S u) (ballCloud y a M) ≤
      ballKineticCoefficient*M^(5/3:ℝ)/a^2-M*coreScreenedField S u y+(5/4:ℝ)*M^2/a := by
  unfold rawThomasFermiEnergy
  rw [ballCloud_power ha hM,coreScreenedField_ballCloud S u hu ha hM y hcore hnuc]
  calc
    _ ≤ ballKineticCoefficient*M^(5/3:ℝ)/a^2-M*coreScreenedField S u y+
        ((5/2:ℝ)*M^2/a)/2 := by
      have H := ballCloud_coulombBilinear_bound ha hM y
      linarith
    _ = _ := by ring

lemma ballCloud_support {a M : ℝ} (y z : Space) (hz : z ∉ Metric.closedBall y a) :
    ballCloud y a M z = 0 := by
  apply uniformBall_support
  simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hz

lemma ballCloud_ne_zero_norm {a M : ℝ} (y z : Space) (hz : ballCloud y a M z ≠ 0) :
    ‖z-y‖ < a := by
  by_contra hn
  apply hz
  change (Metric.ball (0:Space) a).indicator (fun _ => M/(4*Real.pi/3*a^3)) (z-y) = 0
  exact Set.indicator_of_notMem (by simpa only [Metric.mem_ball,dist_zero_right] using hn) _

lemma ballCloud_separated_window {a : ℝ} (ha : 0 < a) (y : Space)
    (g : 𝓢(Space,ℝ)) (hgs : ∀ z, a < ‖z‖ → g z = 0)
    {A : Set Space} (hsep : ∀ z ∈ A, 3*a ≤ ‖z-y‖) :
    Disjoint A (Metric.closedBall y a + tsupport (g : Space → ℝ)) := by
  apply Set.disjoint_left.mpr
  rintro z hz ⟨v,hv,w,hw,rfl⟩
  have hw' : ‖w‖ ≤ a := by
    have H : tsupport (g : Space → ℝ) ⊆ Metric.closedBall 0 a := by
      apply closure_minimal ?_ Metric.isClosed_closedBall
      intro x hx
      simpa only [Metric.mem_closedBall,dist_zero_right] using
        (le_of_not_gt (fun h => hx (hgs x h)) : ‖x‖ ≤ a)
    simpa only [Metric.mem_closedBall,dist_zero_right] using H hw
  have hv' : ‖v-y‖ ≤ a := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hv
  have hnorm : ‖v+w-y‖ ≤ 2*a := by
    calc
      ‖v+w-y‖ = ‖(v-y)+w‖ := by congr 1; abel
      _ ≤ ‖v-y‖+‖w‖ := norm_add_le _ _
      _ ≤ 2*a := by linarith
  linarith [hsep (v+w) hz]

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_ScaledWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

def scaledWindow (g : 𝓢(Space,ℝ)) (a : ℝ) (ha : a ≠ 0) : 𝓢(Space,ℝ) :=
  (Real.sqrt (a^3))⁻¹ • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 a⁻¹ (inv_ne_zero ha))) g

@[simp] lemma scaledWindow_apply (g : 𝓢(Space,ℝ)) (a : ℝ) (ha : a ≠ 0) (x : Space) :
    scaledWindow g a ha x = (Real.sqrt (a^3))⁻¹*g (a⁻¹ • x) := rfl

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise ContDiff
namespace Coulomb

def windowSeed (x : Space) : ℝ := Real.smoothTransition (2*(1-‖x‖^2))

lemma windowSeed_smooth : ContDiff ℝ ∞ windowSeed := by
  apply Real.smoothTransition.contDiff.comp
  exact contDiff_const.mul (contDiff_const.sub (contDiff_norm_sq ℝ))

lemma windowSeed_support (x : Space) (hx : 1 ≤ ‖x‖) : windowSeed x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [norm_nonneg x]

lemma windowSeed_compact : HasCompactSupport windowSeed := by
  apply HasCompactSupport.intro (K := Metric.closedBall 0 1) (isCompact_closedBall 0 1)
  intro x hx
  apply windowSeed_support x
  have hx' : 1 < ‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx
  exact hx'.le

def unitWindow : 𝓢(Space,ℝ) :=
  (Real.sqrt (∫ x : Space, windowSeed x^2))⁻¹ •
    windowSeed_compact.toSchwartzMap windowSeed_smooth

lemma unitWindow_kinetic_nonneg :
    0 ≤ ∑ b : Fin 3, ∫ x : Space, (fderiv ℝ unitWindow x (EuclideanSpace.single b 1))^2 := by
  exact Finset.sum_nonneg (fun b hb => integral_nonneg (fun x => sq_nonneg _))

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PositiveField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
noncomputable section
namespace Coulomb

def ballTrialCoefficient : ℝ := ballKineticCoefficient+
  (1/2:ℝ)*(∑ b : Fin 3, ∫ x : Space, (fderiv ℝ unitWindow x (EuclideanSpace.single b 1))^2)+2

lemma ballTrialCoefficient_pos : 0 < ballTrialCoefficient := by
  unfold ballTrialCoefficient
  linarith [ballKineticCoefficient_pos,unitWindow_kinetic_nonneg]

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ConditionalPositiveField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
noncomputable section
namespace Coulomb

lemma potentialForm_normalized_eq {n : ℕ} (V : Configuration n → ℝ) (u : H1Vector n) :
    potentialForm V u.normalized = (mass u)⁻¹*potentialForm V u := by
  rw [H1Vector.normalized,potentialForm_rsmul,inv_pow,Real.sq_sqrt (mass_nonneg u)]

lemma normalized_corePotential_aestronglyMeasurable {m k : ℕ} (ψ : H1Vector (m+k))
    (s : Spins m) (y : Space) : AEStronglyMeasurable
      (fun x => coreCoulombPotential (ψ.coreSlice s x).normalized y) volume := by
  simp only [←nuclearEnergy_unit_eq_coreCoulomb]
  change AEStronglyMeasurable (fun x => potentialForm (nuclearPotential (unitNucleus y))
    (ψ.coreSlice s x).normalized) _
  simp only [potentialForm_normalized_eq]
  exact (mass_coreSlice_integrable ψ s).aestronglyMeasurable.inv₀.mul
    (potentialForm_coreSlice_integrable ψ s (nuclearPotential (unitNucleus y))
      (fun t => ψ.core_nuclear_integrable (unitNucleus y) (Fin.append s t))).aestronglyMeasurable

lemma coreField_positive_le {J k : ℕ} (S : Nuclei J) (u : H1Vector k) (y : Space) :
    max (coreScreenedField S u y) 0 ≤ attraction S y := by
  apply max_le _ (attraction_nonneg S y)
  unfold coreScreenedField
  linarith [coreCoulombPotential_nonneg u y]

lemma coreField_positive_square_weight_integrable {J m k : ℕ} (S : Nuclei J)
    (ψ : H1Vector (m+k)) (s : Spins m) (y : Space) :
    Integrable (fun x => mass (ψ.coreSlice s x)*(max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2) := by
  have hm : AEStronglyMeasurable (fun x => (max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2) volume := by
    exact ((aestronglyMeasurable_const.sub (normalized_corePotential_aestronglyMeasurable ψ s y)).sup
      aestronglyMeasurable_const).pow 2
  have hb : ∀ᵐ x ∂volume, ‖(max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2‖ ≤ (attraction S y)^2 := by
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (le_max_right _ _) (coreField_positive_le S _ y) 2
  exact (mass_coreSlice_integrable ψ s).mul_bdd hm hb

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_CutJensen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma boundedObservable_integrable {n : ℕ} (u : H1Vector n) (W : Configuration n → ℝ)
    (hW : Measurable W) {B : ℝ} (hB : ∀ x, |W x| ≤ B) (s : Spins n) :
    Integrable (fun x => W x*‖u.value s x‖^2) := by
  exact ((u.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).bdd_mul hW.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hB x))

lemma potentialForm_abs_le {n : ℕ} (u : H1Vector n) (W : Configuration n → ℝ)
    (hW : Measurable W) {B : ℝ} (hB : ∀ x, |W x| ≤ B) :
    |potentialForm W u| ≤ B*mass u := by
  rw [abs_le]
  have h (s : Spins n) : -(B*(∫ x, ‖u.value s x‖^2)) ≤ ∫ x, W x*‖u.value s x‖^2 ∧
      (∫ x, W x*‖u.value s x‖^2) ≤ B*(∫ x, ‖u.value s x‖^2) := by
    constructor
    · rw [← integral_const_mul,← integral_neg]
      apply integral_mono (((u.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul B).neg
        (boundedObservable_integrable u W hW hB s)
      intro x
      have H := (abs_le.mp (hB x)).1
      dsimp only [Pi.neg_apply]
      nlinarith [sq_nonneg ‖u.value s x‖,mul_le_mul_of_nonneg_right H (sq_nonneg ‖u.value s x‖)]
    · rw [← integral_const_mul]
      exact integral_mono (boundedObservable_integrable u W hW hB s)
        (((u.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul B)
        (fun x => mul_le_mul_of_nonneg_right (abs_le.mp (hB x)).2 (sq_nonneg _))
  constructor
  · simpa only [potentialForm,mass,Finset.sum_neg_distrib,←Finset.mul_sum] using
      Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => (h s).1)
  · simpa only [potentialForm,mass,←Finset.mul_sum] using
      Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => (h s).2)

lemma mass_normalized_le_one {n : ℕ} (u : H1Vector n) : mass u.normalized ≤ 1 := by
  by_cases h : mass u=0
  · simp [H1Vector.normalized,mass_rsmul,h]
  · exact (mass_normalized u (lt_of_le_of_ne (mass_nonneg u) (Ne.symm h))).le

def coreConditionalObservable {m k : ℕ} (u : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (s : Spins m) (x : Configuration m) : ℝ :=
  potentialForm (fun v => W (joinConfiguration m k (x,v))) (u.coreSlice s x).normalized

lemma coreConditionalObservable_abs_le {m k : ℕ} (u : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |W x| ≤ B) (s : Spins m) (x : Configuration m) :
    |coreConditionalObservable u W s x| ≤ B := by
  apply (potentialForm_abs_le _ _ (hW.comp ((joinConfiguration m k).continuous.measurable.comp
    (measurable_const.prodMk measurable_id))) (fun v => hB _)).trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (mass_normalized_le_one (u.coreSlice s x)) hB0

lemma coreConditionalObservable_aestronglyMeasurable {m k : ℕ} (u : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB : ∀ x, |W x| ≤ B)
    (s : Spins m) : AEStronglyMeasurable (coreConditionalObservable u W s) volume := by
  unfold coreConditionalObservable
  simp only [potentialForm_normalized_eq]
  apply (mass_coreSlice_integrable u s).aestronglyMeasurable.inv₀.mul
  apply (potentialForm_coreSlice_parameter_integrable u s (fun x v => W (joinConfiguration m k (x,v))) ?_).aestronglyMeasurable
  intro t
  simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply] using
    boundedObservable_integrable u W hW hB (Fin.append s t)

lemma coreConditionalObservable_weight_integrable {m k : ℕ} (u : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |W x| ≤ B) (s : Spins m) :
    Integrable (fun x => mass (u.coreSlice s x)*coreConditionalObservable u W s x) := by
  exact (mass_coreSlice_integrable u s).mul_bdd
    (coreConditionalObservable_aestronglyMeasurable u W hW hB s)
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using
      (coreConditionalObservable_abs_le u W hW hB0 hB s x)))

lemma coreConditionalObservable_positive_weight_integrable {m k : ℕ} (u : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |W x| ≤ B) (s : Spins m) (q : ℕ) :
    Integrable (fun x => mass (u.coreSlice s x)*(max (coreConditionalObservable u W s x) 0)^q) := by
  apply (mass_coreSlice_integrable u s).mul_bdd
    (((coreConditionalObservable_aestronglyMeasurable u W hW hB s).sup aestronglyMeasurable_const).pow q)
  filter_upwards [] with x
  change ‖(max (coreConditionalObservable u W s x) 0)^q‖ ≤ B^q
  rw [Real.norm_of_nonneg (pow_nonneg (le_max_right _ _) q)]
  exact pow_le_pow_left₀ (le_max_right _ _) (max_le (le_trans (le_abs_self _)
    (coreConditionalObservable_abs_le u W hW hB0 hB s x)) hB0) q

lemma sliceExpectation_coreConditionalObservable {m k : ℕ} (u : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB : ∀ x, |W x| ≤ B) :
    sliceExpectation u (coreConditionalObservable u W)=potentialForm W u := by
  unfold sliceExpectation coreConditionalObservable
  simp_rw [potentialForm_normalized_weight]
  have H := integral_potentialForm_coreSlice_parameter u (fun x v => W (joinConfiguration m k (x,v)))
    (fun st => by simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply] using
      boundedObservable_integrable u W hW hB st)
  simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply,potentialForm] using H

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RawObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def rawSignedField {n : ℕ} (V : ℝ) (A : Set Space) (y : Space) (x : Configuration n) : ℝ :=
  V-restrictedOutPotential x A y

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_CutCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma tensorCut_permute_invariant {n : ℕ} {L : Type*} (χ : L → Space → ℝ)
    (p : Fin n → L) (q : Equiv.Perm (Fin n)) (hp : ∀ i, p (q i)=p i) (x : Configuration n) :
    tensorCut χ p (permute q x) = tensorCut χ p x := by
  unfold tensorCut
  simp only [position_permute]
  calc
    _ = ∏ i, χ (p (q i)) (position x (q i)) := by simp only [hp]
    _ = _ := Equiv.prod_comp q (fun i => χ (p i) (position x i))

lemma SpatiallySupported.rsmul {n : ℕ} {u : H1Vector n} {A : Set Space}
    (hu : SpatiallySupported u A) (c : ℝ) : SpatiallySupported (u.rsmul c) A := by
  intro s
  filter_upwards [hu s] with x hx hxA
  change (c:ℂ)*u.value s x=0
  rw [hx hxA,mul_zero]
lemma SpatiallySupported.normalized {n : ℕ} {u : H1Vector n} {A : Set Space}
    (hu : SpatiallySupported u A) : SpatiallySupported u.normalized A := hu.rsmul _

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_SortedCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma Antisymmetric.congr_ae {n : ℕ} {u v : H1Vector n} (hu : Antisymmetric u)
    (he : ∀ s, u.value s =ᵐ[volume] v.value s) : Antisymmetric v := by
  intro p s
  filter_upwards [(permute_measurePreserving p).quasiMeasurePreserving.ae (he (s ∘ p)),he s,hu p s] with x hx hy hz
  change u.value (s ∘ p) (permute p x)=v.value (s ∘ p) (permute p x) at hx
  rw [← hx,← hy]
  exact hz

lemma Antisymmetric.permutation {n : ℕ} {u : H1Vector n} (hu : Antisymmetric u)
    (p : Equiv.Perm (Fin n)) : Antisymmetric (u.permutation p) := by
  apply (antisymmetric_scale u hu (((p.sign:ℤ):ℂ))).congr_ae
  intro s
  filter_upwards [hu p s] with x hx
  exact hx.symm

lemma mass_congr_ae {n : ℕ} (u v : H1Vector n) (he : ∀ s, u.value s =ᵐ[volume] v.value s) :
    mass u=mass v := by
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  filter_upwards [he s] with x hx
  rw [hx]

lemma form_permutation {J n : ℕ} (S : Nuclei J) (u : H1Vector n) (p : Equiv.Perm (Fin n)) :
    form S (u.permutation p)=form S u := by
  change kinetic (u.permutation p)-potentialEnergy (nuclearPotential S) (u.permutation p)+
    potentialEnergy pairPotential (u.permutation p)=_
  rw [kinetic_permutation,potentialEnergy_permutation _ (nuclearPotential_permute S),
    potentialEnergy_permutation _ pairPotential_permute]
  rfl

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_RadialCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff
namespace Coulomb

def cutSeed (x : Space) : ℝ := Real.smoothTransition ((4-‖x‖^2)/3)
lemma cutSeed_smooth : ContDiff ℝ ∞ cutSeed := by
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const 3)
lemma cutSeed_zero (x : Space) (hx : 2 ≤ ‖x‖) : cutSeed x=0 := by
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [norm_nonneg x]
lemma cutSeed_compact : HasCompactSupport cutSeed := by
  apply HasCompactSupport.intro (K := Metric.closedBall 0 2) (isCompact_closedBall 0 2)
  intro x hx
  exact cutSeed_zero x (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using le_of_lt (show 2 < ‖x‖ by simpa using hx))

lemma cutSeed_derivative_bounded : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖fderiv ℝ cutSeed x‖ ≤ C := by
  obtain ⟨B,hB⟩ := (cutSeed_compact.fderiv ℝ).exists_bound_of_continuous
    (cutSeed_smooth.continuous_fderiv (by simp))
  exact ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun x => (hB x).trans (le_max_left _ _)⟩
def cutSeedDerivativeBound : ℝ := Classical.choose cutSeed_derivative_bounded
lemma cutSeedDerivativeBound_pos : 0 < cutSeedDerivativeBound := (Classical.choose_spec cutSeed_derivative_bounded).1
lemma norm_cutSeed_derivative (x : Space) : ‖fderiv ℝ cutSeed x‖ ≤ cutSeedDerivativeBound :=
  (Classical.choose_spec cutSeed_derivative_bounded).2 x

def cutAngle (y : Space) (r : ℝ) (x : Space) : ℝ := (Real.pi/2)*cutSeed (r⁻¹ • (x-y))
lemma cutAngle_smooth (y : Space) (r : ℝ) : ContDiff ℝ ∞ (cutAngle y r) := by
  have ht : ContDiff ℝ ∞ (fun x : Space => r⁻¹ • (x-y)) := by fun_prop
  exact contDiff_const.mul (cutSeed_smooth.comp ht)
lemma cutAngle_fderiv (y : Space) (r : ℝ) (x v : Space) :
    fderiv ℝ (cutAngle y r) x v = (Real.pi/2)*r⁻¹*fderiv ℝ cutSeed (r⁻¹ • (x-y)) v := by
  have ht : HasFDerivAt (fun x : Space => r⁻¹ • (x-y))
      (r⁻¹ • (ContinuousLinearMap.id ℝ Space)) x := by
    convert ((hasFDerivAt_id x).sub_const y).const_smul r⁻¹ using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have h := (((cutSeed_smooth.differentiable (by simp) _).hasFDerivAt.comp x ht).const_mul (Real.pi/2)).fderiv
  have hh : fderiv ℝ (cutAngle y r) x =
      (Real.pi/2) • ((fderiv ℝ cutSeed (r⁻¹ • (x-y))).comp (r⁻¹ • ContinuousLinearMap.id ℝ Space)) := by
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  rw [hh]
  simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,map_smul]
  ring

def radialCut (y : Space) (r : ℝ) (l : Fin 2) (x : Space) : ℝ :=
  if l=0 then Real.sin (cutAngle y r x) else Real.cos (cutAngle y r x)
lemma radialCut_smooth (y : Space) (r : ℝ) (l : Fin 2) : ContDiff ℝ ∞ (radialCut y r l) := by
  unfold radialCut
  split_ifs
  · exact (cutAngle_smooth y r).sin
  · exact (cutAngle_smooth y r).cos
lemma radialCut_partition (y : Space) (r : ℝ) (x : Space) :
    ∑ l : Fin 2, radialCut y r l x ^ 2 = 1 := by
  simp [Fin.sum_univ_two,radialCut]

def radialCutCoefficient : ℝ := (Real.pi/2)*cutSeedDerivativeBound
lemma radialCutCoefficient_pos : 0 < radialCutCoefficient := by
  exact mul_pos (by positivity) cutSeedDerivativeBound_pos
lemma radialCut_derivative_bound (y : Space) {r : ℝ} (hr : 0 < r) (l : Fin 2)
    (b : Fin 3) (x : Space) :
    |fderiv ℝ (radialCut y r l) x (EuclideanSpace.single b 1)| ≤ radialCutCoefficient/r := by
  have hb : |fderiv ℝ (cutAngle y r) x (EuclideanSpace.single b 1)| ≤ radialCutCoefficient/r := by
    rw [cutAngle_fderiv,abs_mul,abs_of_pos (mul_pos (by positivity) (inv_pos.mpr hr))]
    have H := ((fderiv ℝ cutSeed (r⁻¹ • (x-y))).le_opNorm (EuclideanSpace.single b 1)).trans
      (mul_le_mul_of_nonneg_right (norm_cutSeed_derivative _) (norm_nonneg _))
    simp only [PiLp.norm_single,norm_one,mul_one,Real.norm_eq_abs] at H
    calc
      _ ≤ (Real.pi/2)*r⁻¹*cutSeedDerivativeBound := mul_le_mul_of_nonneg_left H (by positivity)
      _ = radialCutCoefficient/r := by unfold radialCutCoefficient; ring
  unfold radialCut
  split_ifs
  · rw [fderiv_sin ((cutAngle_smooth y r).differentiable (by simp) x)]
    simp only [smul_apply,smul_eq_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans (by simpa using hb)
  · rw [fderiv_cos ((cutAngle_smooth y r).differentiable (by simp) x)]
    simp only [smul_apply,smul_eq_mul,abs_mul,abs_neg]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans (by simpa using hb)

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
namespace Coulomb

lemma radialCut_fderiv_zero (y : Space) {r : ℝ} (hr : 0 < r) (l : Fin 2)
    (x : Space) (hx : 2*r < ‖x-y‖) : fderiv ℝ (radialCut y r l) x=0 := by
  have he : radialCut y r l =ᶠ[𝓝 x] (fun _ => if l=0 then (0:ℝ) else 1) := by
    have hh : ∀ᶠ z in 𝓝 x, 2*r < ‖z-y‖ :=
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hx
    filter_upwards [hh] with z hz
    have hs : 2 ≤ ‖r⁻¹ • (z-y)‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
      exact (le_inv_mul_iff₀ hr).2 (by nlinarith)
    simp only [radialCut,cutAngle,cutSeed_zero _ hs,mul_zero,Real.sin_zero,Real.cos_zero]
  rw [he.fderiv_eq]
  simp

lemma radialCut_gradient_bound (y : Space) {r : ℝ} (hr : 0 < r) (b : Fin 3) (x : Space) :
    (∑ l : Fin 2, (fderiv ℝ (radialCut y r l) x (EuclideanSpace.single b 1))^2) ≤
      (2*(radialCutCoefficient/r)^2) * (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) x := by
  by_cases hx : x ∈ Metric.closedBall y (2*r)
  · rw [indicator_of_mem hx,mul_one]
    calc
      _ ≤ ∑ _l : Fin 2, (radialCutCoefficient/r)^2 := by
        apply Finset.sum_le_sum
        intro l hl
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (div_nonneg radialCutCoefficient_pos.le hr.le)).2
          (radialCut_derivative_bound y hr l b x)
      _ = _ := by simp
  · rw [indicator_of_notMem hx,mul_zero]
    have hd := radialCut_fderiv_zero y hr
    have hh : 2*r < ‖x-y‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hx
    simp only [hd _ x hh,zero_apply,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
      zero_pow,Finset.sum_const_zero,le_refl]

def expectedPopulation {n : ℕ} (ψ : H1Vector n) (A : Set Space) : ℝ :=
  ∑ s, ∑ i : Fin n, ∫ x, (A.indicator (fun _ => (1:ℝ)) (position x i))*‖ψ.value s x‖^2

lemma population_integrable {n : ℕ} (ψ : H1Vector n) (A : Set Space) (hA : MeasurableSet A)
    (s : Spins n) (i : Fin n) :
    Integrable (fun x => (A.indicator (fun _ => (1:ℝ)) (position x i))*‖ψ.value s x‖^2) := by
  have H := ((ψ.value_L2 s).integrable_norm_pow (by norm_num)).indicator (hA.preimage (positionCLM i).continuous.measurable)
  apply H.congr
  filter_upwards [] with x
  change (if position x i ∈ A then ‖ψ.value s x‖^2 else 0) = _
  by_cases hx : position x i ∈ A <;> simp [hx]

theorem form_radial_labelCut {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    (y : Space) {r : ℝ} (hr : 0 < r) :
    (∑ p : Fin n → Fin 2, form S (ψ.labelCut (radialCut y r) (radialCut_smooth y r)
      (radialCut_partition y r) (radialCutCoefficient/r) (div_nonneg radialCutCoefficient_pos.le hr.le)
      (radialCut_derivative_bound y hr) p)) ≤
      form S ψ+3*(radialCutCoefficient/r)^2*expectedPopulation ψ (Metric.closedBall y (2*r)) := by
  rw [form_labelCut]
  apply add_le_add_right
  let c : ℝ := 2*(radialCutCoefficient/r)^2
  have hi s i := population_integrable ψ (Metric.closedBall y (2*r)) measurableSet_closedBall s i
  have H (s : Spins n) (a : Fin n × Fin 3) :
      (∫ x, (∑ l, (fderiv ℝ (radialCut y r l) (position x a.1) (EuclideanSpace.single a.2 1))^2)*‖ψ.value s x‖^2) ≤
      c*(∫ x, (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · filter_upwards [] with x
      exact mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
    · exact (hi s a.1).const_mul c
    · filter_upwards [] with x
      simpa only [c,mul_assoc] using mul_le_mul_of_nonneg_right (radialCut_gradient_bound y hr a.2 (position x a.1)) (sq_nonneg ‖ψ.value s x‖)
  calc
    _ ≤ (1/2:ℝ)*∑ s, ∑ a : Fin n × Fin 3, c*(∫ x,
          (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun a _ => H s a))) (by norm_num)
    _ = _ := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ← Finset.mul_sum,expectedPopulation,c]
      ring

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CountMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def localCount {n : ℕ} (A : Set Space) (x : Configuration n) : ℝ :=
  ∑ i : Fin n, A.indicator (fun _ => (1:ℝ)) (position x i)

lemma localCount_nonneg {n : ℕ} (A : Set Space) (x : Configuration n) : 0 ≤ localCount A x := by
  exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
lemma localCount_le {n : ℕ} (A : Set Space) (x : Configuration n) : localCount A x ≤ n := by
  calc
    _ ≤ ∑ _i : Fin n, (1:ℝ) := Finset.sum_le_sum (fun i _ => by
      by_cases h : position x i ∈ A <;> simp [h])
    _ = _ := by simp
lemma localCount_measurable {n : ℕ} {A : Set Space} (hA : MeasurableSet A) :
    Measurable (localCount (n:=n) A) := by
  exact Finset.measurable_fun_sum _ (fun i _ => (measurable_const.indicator hA).comp (continuous_position i).measurable)

lemma expectedPopulation_eq {n : ℕ} (ψ : H1Vector n) {A : Set Space} (hA : MeasurableSet A) :
    expectedPopulation ψ A = ∑ s : Spins n, ∫ x, localCount A x*‖ψ.value s x‖^2 := by
  apply Finset.sum_congr rfl
  intro s hs
  simp only [localCount,Finset.sum_mul]
  exact (integral_finsetSum _ (fun i _ => population_integrable ψ A hA s i)).symm

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SortedObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def reindexConfiguration {m n : ℕ} (e : Fin m ≃ Fin n) (x : Configuration m) : Configuration n :=
  WithLp.toLp 2 (fun ib => x (e.symm ib.1,ib.2))

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_RecordReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def H1Vector.reindex {m n : ℕ} (u : H1Vector n) (e : Fin m ≃ Fin n) : H1Vector m := by
  have h : m=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  exact u.permutation e.symm

lemma H1Vector.reindex_value {m n : ℕ} (u : H1Vector n) (e : Fin m ≃ Fin n)
    (s : Spins m) (x : Configuration m) :
    (u.reindex e).value s x=u.value (s ∘ e.symm) (reindexConfiguration e x) := by
  have h : m=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  rfl

lemma mass_reindex {m n : ℕ} (u : H1Vector n) (e : Fin m ≃ Fin n) :
    mass (u.reindex e)=mass u := by
  have h : m=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  exact mass_permutation _ _

lemma form_reindex {J m n : ℕ} (S : Nuclei J) (u : H1Vector n) (e : Fin m ≃ Fin n) :
    form S (u.reindex e)=form S u := by
  have h : m=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  exact form_permutation _ _ _

def recordAssoc (m q k : ℕ) : Fin ((m+q)+k) ≃ Fin (m+(q+k)) :=
  finSumFinEquiv.symm.trans (((finSumFinEquiv.symm.sumCongr (Equiv.refl _)).trans
    (Equiv.sumAssoc (Fin m) (Fin q) (Fin k))).trans
      ((Equiv.refl _).sumCongr finSumFinEquiv |>.trans finSumFinEquiv))

lemma recordAssoc_left (m q k : ℕ) (i : Fin m) :
    recordAssoc m q k (Fin.castAdd k (Fin.castAdd q i))=Fin.castAdd (q+k) i := by
  simp only [recordAssoc,Equiv.trans_apply,←finSumFinEquiv_apply_left,Equiv.symm_apply_apply,
    Equiv.sumCongr_apply,Sum.map_inl,Equiv.sumAssoc_apply_inl_inl,Equiv.refl_apply]

lemma recordAssoc_middle (m q k : ℕ) (i : Fin q) :
    recordAssoc m q k (Fin.castAdd k (Fin.natAdd m i))=Fin.natAdd m (Fin.castAdd k i) := by
  simp only [recordAssoc,Equiv.trans_apply,←finSumFinEquiv_apply_left,←finSumFinEquiv_apply_right,
    Equiv.symm_apply_apply,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,
    Equiv.sumAssoc_apply_inl_inr]

lemma recordAssoc_right (m q k : ℕ) (i : Fin k) :
    recordAssoc m q k (Fin.natAdd (m+q) i)=Fin.natAdd m (Fin.natAdd q i) := by
  simp only [recordAssoc,Equiv.trans_apply,←finSumFinEquiv_apply_right,
    Equiv.symm_apply_apply,Equiv.sumCongr_apply,Sum.map_inr,
    Equiv.sumAssoc_apply_inr,Equiv.refl_apply]

lemma append_recordAssoc {m q k : ℕ} (s : Spins m) (t : Spins q) (r : Spins k) :
    (Fin.append (Fin.append s t) r) ∘ (recordAssoc m q k).symm=Fin.append s (Fin.append t r) := by
  funext i
  obtain ⟨j,rfl⟩ := (recordAssoc m q k).surjective i
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · simp only [recordAssoc_left,Fin.append_left]
    · simp only [recordAssoc_middle,Fin.append_left,Fin.append_right]
  · simp only [recordAssoc_right,Fin.append_right]

lemma reindex_join_recordAssoc {m q k : ℕ} (x : Configuration m) (y : Configuration q)
    (z : Configuration k) :
    reindexConfiguration (recordAssoc m q k) (joinConfiguration (m+q) k (joinConfiguration m q (x,y),z))=
      joinConfiguration m (q+k) (x,joinConfiguration q k (y,z)) := by
  ext ⟨i,b⟩
  obtain ⟨j,rfl⟩ := (recordAssoc m q k).surjective i
  change joinConfiguration (m+q) k (joinConfiguration m q (x,y),z)
    ((recordAssoc m q k).symm (recordAssoc m q k j),b)=_
  rw [Equiv.symm_apply_apply]
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · rw [recordAssoc_left,joinConfiguration_left,joinConfiguration_left,joinConfiguration_left]
    · rw [recordAssoc_middle,joinConfiguration_left,joinConfiguration_right,
        joinConfiguration_right,joinConfiguration_left]
  · rw [recordAssoc_right,joinConfiguration_right,joinConfiguration_right,joinConfiguration_right]

lemma reindexConfiguration_continuous {m n : ℕ} (e : Fin m ≃ Fin n) :
    Continuous (reindexConfiguration e) := by
  have h : m=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  exact (permuteIsometry e.symm).continuous

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_CutRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma positive_square_tangent (b c : ℝ) (hc : 0 ≤ c) :
    2*c*b-c^2 ≤ (max b 0)^2 := by
  nlinarith [sq_nonneg (max b 0-c),mul_le_mul_of_nonneg_left (le_max_left b 0) hc]

lemma finite_mass_positive_jensen {P : Type*} [Fintype P]
    (M H : P → ℝ) (hM : ∀ p, 0≤M p) (m h : ℝ)
    (hm : ∑ p, M p=m) (hh : ∑ p, M p*H p=m*h) :
    m*(max h 0)^2 ≤ ∑ p, M p*(max (H p) 0)^2 := by
  let c := max h 0
  have hc : 0 ≤ c := le_max_right _ _
  have H0 := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (positive_square_tangent (H p) c hc) (hM p))
  have he : (∑ p, M p*(2*c*H p-c^2))=2*c*(m*h)-c^2*m := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    have h1 : (∑ p, M p*(2*c*H p))=2*c*∑ p, M p*H p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    rw [h1,←Finset.sum_mul,hh,hm]
    ring
  rw [he] at H0
  by_cases hp : 0≤h
  · have hec : c=h := max_eq_left hp
    rw [hec] at H0
    rw [max_eq_left hp]
    nlinarith
  · have hec : c=0 := max_eq_right (le_of_not_ge hp)
    rw [hec] at H0
    rw [max_eq_right (le_of_not_ge hp)]
    nlinarith

lemma labelCut_coreSlice_law {m k : ℕ} {L : Type*} [Fintype L]
    (u : H1Vector (m+k)) (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (s : Spins m) :
    ∀ᵐ x, ∀ t : Spins k, ∀ v : Configuration k,
      (∑ p : Fin (m+k) → L,
        ‖((u.labelCut χ hχ hp D hD hd p).coreSlice s x).value t v‖^2)=
          ‖(u.coreSlice s x).value t v‖^2 := by
  have hall : ∀ᵐ x, ∀ p : Fin (m+k) → L,
      (u.labelCut χ hχ hp D hD hd p).CoreSliceRegular s x :=
    ae_all_iff.mpr (fun p => (u.labelCut χ hχ hp D hD hd p).coreSliceRegular_ae s)
  filter_upwards [u.coreSliceRegular_ae s,hall] with x hx ha
  intro t v
  simp_rw [(u.labelCut χ hχ hp D hD hd _).coreSlice_value s (ha _) t v]
  rw [u.coreSlice_value s hx]
  simp only [H1Vector.labelCut,H1Vector.smoothMul,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,
    ←Finset.sum_mul,tensorCut_partition χ hp,one_mul]

lemma fiber_mass_law {P : Type*} [Fintype P] {k : ℕ}
    (u : H1Vector k) (v : P → H1Vector k)
    (hlaw : ∀ s x, (∑ p, ‖(v p).value s x‖^2)=‖u.value s x‖^2) :
    (∑ p, mass (v p))=mass u := by
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [←integral_finsetSum _ (fun p _ => ((v p).value_L2 s).integrable_norm_pow (by norm_num))]
  exact integral_congr_ae (Eventually.of_forall (hlaw s))

lemma fiber_potential_law {P : Type*} [Fintype P] {k : ℕ}
    (u : H1Vector k) (v : P → H1Vector k)
    (hlaw : ∀ s x, (∑ p, ‖(v p).value s x‖^2)=‖u.value s x‖^2)
    (W : Configuration k → ℝ) (hW : Measurable W) {B : ℝ} (hB : ∀ x, |W x| ≤ B) :
    (∑ p, potentialForm W (v p))=potentialForm W u := by
  unfold potentialForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [←integral_finsetSum _ (fun p _ => boundedObservable_integrable (v p) W hW hB s)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [←Finset.mul_sum,hlaw]

theorem labelCut_conditional_positive_jensen {m k : ℕ} {L : Type*} [Fintype L]
    (u : H1Vector (m+k)) (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB0 : 0≤B)
    (hB : ∀ x, |W x| ≤ B) :
    sliceExpectation u (fun s x => (max (coreConditionalObservable u W s x) 0)^2) ≤
      ∑ p : Fin (m+k) → L, sliceExpectation (u.labelCut χ hχ hp D hD hd p)
        (fun s x => (max (coreConditionalObservable (u.labelCut χ hχ hp D hD hd p) W s x) 0)^2) := by
  let v := fun p : Fin (m+k) → L => u.labelCut χ hχ hp D hD hd p
  unfold sliceExpectation
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_finsetSum _ (fun p _ => coreConditionalObservable_positive_weight_integrable (v p) W hW hB0 hB s 2)]
  apply integral_mono_ae (coreConditionalObservable_positive_weight_integrable u W hW hB0 hB s 2)
    (integrable_finsetSum _ (fun p _ => coreConditionalObservable_positive_weight_integrable (v p) W hW hB0 hB s 2))
  filter_upwards [labelCut_coreSlice_law u χ hχ hp D hD hd s] with x hx
  apply finite_mass_positive_jensen (fun p => mass ((v p).coreSlice s x))
    (fun p => coreConditionalObservable (v p) W s x) (fun p => mass_nonneg _) _ _
  · exact fiber_mass_law _ _ hx
  · simp only [coreConditionalObservable,potentialForm_normalized_weight]
    exact fiber_potential_law _ _ hx _
      (hW.comp ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
      (fun _ => hB _)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_RecordJensen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma slice_positive_square_jensen {m k : ℕ} (u : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ}
    (hB0 : 0≤B) (hB : ∀ x, |W x| ≤ B) :
    mass u*(max (potentialForm W u.normalized) 0)^2 ≤
      sliceExpectation u (fun s x => (max (coreConditionalObservable u W s x) 0)^2) := by
  let c := max (potentialForm W u.normalized) 0
  have hc : 0 ≤ c := le_max_right _ _
  have hi (s : Spins m) : Integrable (fun x => mass (u.coreSlice s x)*
      (2*c*coreConditionalObservable u W s x-c^2)) := by
    have H := (coreConditionalObservable_weight_integrable u W hW hB0 hB s).const_mul (2*c)
    have K := (mass_coreSlice_integrable u s).mul_const (c^2)
    apply (H.sub K).congr
    exact Eventually.of_forall (fun x => by dsimp only [Pi.sub_apply]; ring)
  have H0 : sliceExpectation u (fun s x => 2*c*coreConditionalObservable u W s x-c^2) ≤
      sliceExpectation u (fun s x => (max (coreConditionalObservable u W s x) 0)^2) := by
    apply Finset.sum_le_sum
    intro s hs
    exact integral_mono (hi s) (coreConditionalObservable_positive_weight_integrable u W hW hB0 hB s 2)
      (fun x => mul_le_mul_of_nonneg_left (positive_square_tangent _ c hc) (mass_nonneg _))
  have he (s : Spins m) : (∫ x, mass (u.coreSlice s x)*(2*c*coreConditionalObservable u W s x-c^2))=
      2*c*(∫ x, mass (u.coreSlice s x)*coreConditionalObservable u W s x)-c^2*(∫ x, mass (u.coreSlice s x)) := by
    calc
      _ = ∫ x, 2*c*(mass (u.coreSlice s x)*coreConditionalObservable u W s x)-c^2*mass (u.coreSlice s x) := by congr 1; funext x; ring
      _ = _ := by rw [integral_sub ((coreConditionalObservable_weight_integrable u W hW hB0 hB s).const_mul _)
        ((mass_coreSlice_integrable u s).const_mul _),integral_const_mul,integral_const_mul]
  have hs : sliceExpectation u (fun s x => 2*c*coreConditionalObservable u W s x-c^2)=
      2*c*potentialForm W u-c^2*mass u := by
    unfold sliceExpectation
    simp_rw [he]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,integral_mass_coreSlice]
    rw [show (∑ s, ∫ x, mass (u.coreSlice s x)*coreConditionalObservable u W s x)=potentialForm W u from
      sliceExpectation_coreConditionalObservable u W hW hB]
  rw [hs] at H0
  have hw := potentialForm_normalized_weight W u
  by_cases hp : 0≤potentialForm W u.normalized
  · have hec : c=potentialForm W u.normalized := max_eq_left hp
    rw [hec] at H0
    rw [max_eq_left hp]
    nlinarith
  · have hec : c=0 := max_eq_right (le_of_not_ge hp)
    rw [hec] at H0
    rw [max_eq_right (le_of_not_ge hp)]
    nlinarith

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma potentialForm_congr_values {k : ℕ} (W : Configuration k → ℝ) (u v : H1Vector k)
    (hv : ∀ t, u.value t =ᵐ[volume] v.value t) : potentialForm W u=potentialForm W v := by
  apply Finset.sum_congr rfl
  intro t ht
  apply integral_congr_ae
  filter_upwards [hv t] with z hz
  rw [hz]

lemma potentialForm_normalized_congr_values {k : ℕ} (W : Configuration k → ℝ)
    (u v : H1Vector k) (hv : ∀ t, u.value t =ᵐ[volume] v.value t) :
    potentialForm W u.normalized=potentialForm W v.normalized := by
  rw [potentialForm_normalized_eq,potentialForm_normalized_eq,
    mass_congr_ae u v hv,potentialForm_congr_values W u v hv]

lemma nested_coreSlice_values {m q k : ℕ} (u : H1Vector (m+(q+k)))
    (s : Spins m) (t : Spins q) :
    ∀ᵐ x : Configuration m, ∀ᵐ y : Configuration q,
      ∀ r : Spins k, ∀ z : Configuration k,
        ((u.coreSlice s x).coreSlice t y).value r z=
          ((u.reindex (recordAssoc m q k)).coreSlice (Fin.append s t)
            (joinConfiguration m q (x,y))).value r z := by
  let v := u.reindex (recordAssoc m q k)
  have hd : ∀ᵐ x : Configuration m, ∀ᵐ y : Configuration q,
      v.CoreSliceRegular (Fin.append s t) (joinConfiguration m q (x,y)) :=
    Measure.ae_ae_of_ae_prod ((joinConfiguration_measurePreserving m q).quasiMeasurePreserving.ae
      (v.coreSliceRegular_ae (Fin.append s t)))
  filter_upwards [u.coreSliceRegular_ae s,hd] with x hx hd
  filter_upwards [(u.coreSlice s x).coreSliceRegular_ae t,hd] with y hy hd
  intro r z
  rw [(u.coreSlice s x).coreSlice_value t hy,u.coreSlice_value s hx,v.coreSlice_value (Fin.append s t) hd]
  simp only [v,H1Vector.reindex_value,append_recordAssoc,reindex_join_recordAssoc]

lemma nested_coreConditional_weight {m q k : ℕ} (u : H1Vector (m+(q+k)))
    (W : Configuration (m+(q+k)) → ℝ) (s : Spins m) (t : Spins q) :
    ∀ᵐ x : Configuration m, ∀ᵐ y : Configuration q,
      mass ((u.coreSlice s x).coreSlice t y)*
        (max (coreConditionalObservable (u.coreSlice s x)
          (fun w => W (joinConfiguration m (q+k) (x,w))) t y) 0)^2 =
      mass ((u.reindex (recordAssoc m q k)).coreSlice (Fin.append s t) (joinConfiguration m q (x,y)))*
        (max (coreConditionalObservable (u.reindex (recordAssoc m q k))
          (W ∘ reindexConfiguration (recordAssoc m q k)) (Fin.append s t) (joinConfiguration m q (x,y))) 0)^2 := by
  filter_upwards [nested_coreSlice_values u s t] with x hx
  filter_upwards [hx] with y hy
  have hv : ∀ r, ((u.coreSlice s x).coreSlice t y).value r =ᵐ[volume]
      ((u.reindex (recordAssoc m q k)).coreSlice (Fin.append s t) (joinConfiguration m q (x,y))).value r :=
    fun r => Eventually.of_forall (hy r)
  rw [mass_congr_ae _ _ hv]
  congr 2
  unfold coreConditionalObservable
  simp only [Function.comp_apply,reindex_join_recordAssoc]
  exact congrArg (fun b : ℝ => max b 0)
    (potentialForm_normalized_congr_values _ _ _ hv)

theorem record_more_positive_jensen {m q k : ℕ} (u : H1Vector (m+(q+k)))
    (W : Configuration (m+(q+k)) → ℝ) (hW : Measurable W) {B : ℝ}
    (hB0 : 0≤B) (hB : ∀ x, |W x| ≤ B) :
    sliceExpectation u (fun s x => (max (coreConditionalObservable u W s x) 0)^2) ≤
      sliceExpectation (u.reindex (recordAssoc m q k)) (fun s x =>
        (max (coreConditionalObservable (u.reindex (recordAssoc m q k))
          (W ∘ reindexConfiguration (recordAssoc m q k)) s x) 0)^2) := by
  let v := u.reindex (recordAssoc m q k)
  let V := W ∘ reindexConfiguration (recordAssoc m q k)
  have hV : Measurable V := hW.comp (reindexConfiguration_continuous _).measurable
  let F := fun (s : Spins m) (t : Spins q) (x : Configuration m) (y : Configuration q) =>
    mass (v.coreSlice (Fin.append s t) (joinConfiguration m q (x,y)))*
      (max (coreConditionalObservable v V (Fin.append s t) (joinConfiguration m q (x,y))) 0)^2
  have hi (s : Spins m) (t : Spins q) : Integrable (fun xy : Configuration m × Configuration q => F s t xy.1 xy.2)
      (volume.prod volume) := by
    exact ((joinConfiguration_measurePreserving m q).integrable_comp_emb
      (joinConfiguration m q).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr
      (coreConditionalObservable_positive_weight_integrable v V hV hB0 (fun x => hB _) (Fin.append s t) 2)
  have hstep (s : Spins m) :
      (∫ x, mass (u.coreSlice s x)*(max (coreConditionalObservable u W s x) 0)^2) ≤
        ∑ t : Spins q, ∫ xy, mass (v.coreSlice (Fin.append s t) xy)*
          (max (coreConditionalObservable v V (Fin.append s t) xy) 0)^2 := by
    calc
      _ ≤ ∫ x, ∑ t, ∫ y, F s t x y := by
        apply integral_mono_ae (coreConditionalObservable_positive_weight_integrable u W hW hB0 hB s 2)
          (integrable_finsetSum _ (fun t _ => (hi s t).integral_prod_left))
        have hall : ∀ᵐ x : Configuration m, ∀ t : Spins q,
            ∀ᵐ y : Configuration q,
              mass ((u.coreSlice s x).coreSlice t y)*
                (max (coreConditionalObservable (u.coreSlice s x)
                  (fun w => W (joinConfiguration m (q+k) (x,w))) t y) 0)^2=F s t x y :=
          ae_all_iff.mpr (fun t => nested_coreConditional_weight u W s t)
        filter_upwards [hall] with x hx
        have H := slice_positive_square_jensen (u.coreSlice s x)
          (fun w => W (joinConfiguration m (q+k) (x,w)))
          (hW.comp ((joinConfiguration m (q+k)).continuous.measurable.comp
            (measurable_const.prodMk measurable_id))) hB0 (fun w => hB _)
        change mass (u.coreSlice s x)*(max (coreConditionalObservable u W s x) 0)^2 ≤ _ at H
        apply H.trans_eq
        exact Finset.sum_congr rfl (fun t _ => integral_congr_ae (hx t))
      _ = ∑ t, ∫ xy : Configuration m × Configuration q, F s t xy.1 xy.2 ∂volume.prod volume := by
        rw [integral_finsetSum _ (fun t _ => (hi s t).integral_prod_left)]
        exact Finset.sum_congr rfl (fun t _ => (integral_prod _ (hi s t)).symm)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        exact (joinConfiguration_measurePreserving m q).integral_comp' (fun xy : Configuration (m+q) =>
          mass (v.coreSlice (Fin.append s t) xy)*(max (coreConditionalObservable v V (Fin.append s t) xy) 0)^2)
  calc
    _ ≤ ∑ s : Spins m, ∑ t : Spins q, ∫ x, mass (v.coreSlice (Fin.append s t) x)*
        (max (coreConditionalObservable v V (Fin.append s t) x) 0)^2 :=
      Finset.sum_le_sum (fun s (_ : s∈Finset.univ) => hstep s)
    _ = _ := by
      unfold sliceExpectation
      rw [←Fintype.sum_prod_type (f:=fun st : Spins m × Spins q => ∫ x,
        mass (v.coreSlice (Fin.append st.1 st.2) x)*(max (coreConditionalObservable v V (Fin.append st.1 st.2) x) 0)^2)]
      exact Fintype.sum_equiv (Fin.appendEquiv m q) _ _ (fun _ => rfl)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CoreReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma potentialForm_reindex {m n : ℕ} (u : H1Vector n) (e : Fin m ≃ Fin n)
    (W : Configuration n → ℝ) :
    potentialForm (W ∘ reindexConfiguration e) (u.reindex e)=potentialForm W u := by
  have h : m=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  unfold potentialForm
  have he (s : Spins m) : (∫ x, (W ∘ reindexConfiguration e) x*‖(u.reindex e).value s x‖^2)=
      ∫ x, W x*‖u.value (s ∘ e.symm) x‖^2 := by
    simpa only [Function.comp_apply,H1Vector.reindex_value,reindexConfiguration,permute] using
      (permute_integral_real e.symm (fun x => W x*‖u.value (s ∘ e.symm) x‖^2))
  simp_rw [he]
  exact Equiv.sum_comp (permutationSpins e.symm) (fun s => ∫ x, W x*‖u.value s x‖^2)

def coreReindex (m : ℕ) {q k : ℕ} (e : Fin q ≃ Fin k) : Fin (m+q) ≃ Fin (m+k) :=
  finSumFinEquiv.symm.trans (((Equiv.refl (Fin m)).sumCongr e).trans finSumFinEquiv)

lemma coreReindex_left (m : ℕ) {q k : ℕ} (e : Fin q ≃ Fin k) (i : Fin m) :
    coreReindex m e (Fin.castAdd q i)=Fin.castAdd k i := by simp [coreReindex]
lemma coreReindex_right (m : ℕ) {q k : ℕ} (e : Fin q ≃ Fin k) (i : Fin q) :
    coreReindex m e (Fin.natAdd m i)=Fin.natAdd m (e i) := by simp [coreReindex]
lemma coreReindex_symm (m : ℕ) {q k : ℕ} (e : Fin q ≃ Fin k) :
    (coreReindex m e).symm=coreReindex m e.symm := by
  apply Equiv.symm_bijective.injective
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [coreReindex]

lemma append_coreReindex {m q k : ℕ} (e : Fin q ≃ Fin k) (s : Spins m) (t : Spins q) :
    (Fin.append s t) ∘ (coreReindex m e).symm=Fin.append s (t ∘ e.symm) := by
  rw [coreReindex_symm]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [coreReindex_left,coreReindex_right]

lemma reindex_join_coreReindex {m q k : ℕ} (e : Fin q ≃ Fin k) (x : Configuration m)
    (y : Configuration q) :
    reindexConfiguration (coreReindex m e) (joinConfiguration m q (x,y))=
      joinConfiguration m k (x,reindexConfiguration e y) := by
  ext ⟨i,b⟩
  change joinConfiguration m q (x,y) ((coreReindex m e).symm i,b)=_
  rw [coreReindex_symm]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [coreReindex_left,joinConfiguration_left,joinConfiguration_left]
  · rw [coreReindex_right,joinConfiguration_right,joinConfiguration_right]
    rfl

lemma coreSlice_coreReindex_values {m q k : ℕ} (u : H1Vector (m+k))
    (e : Fin q ≃ Fin k) (s : Spins m) :
    ∀ᵐ x : Configuration m, ∀ t : Spins q, ∀ z : Configuration q,
      ((u.reindex (coreReindex m e)).coreSlice s x).value t z=
        ((u.coreSlice s x).reindex e).value t z := by
  filter_upwards [u.coreSliceRegular_ae s,
    (u.reindex (coreReindex m e)).coreSliceRegular_ae s] with x hx hv
  intro t z
  rw [(u.reindex (coreReindex m e)).coreSlice_value s hv,H1Vector.reindex_value,
    append_coreReindex,reindex_join_coreReindex,H1Vector.reindex_value,u.coreSlice_value s hx]

lemma coreConditionalObservable_coreReindex {m q k : ℕ} (u : H1Vector (m+k))
    (e : Fin q ≃ Fin k) (W : Configuration (m+k) → ℝ) (s : Spins m) :
    ∀ᵐ x : Configuration m,
      mass ((u.reindex (coreReindex m e)).coreSlice s x)=mass (u.coreSlice s x) ∧
      coreConditionalObservable (u.reindex (coreReindex m e))
        (W ∘ reindexConfiguration (coreReindex m e)) s x=coreConditionalObservable u W s x := by
  filter_upwards [coreSlice_coreReindex_values u e s] with x hx
  have hv : ∀ t, ((u.reindex (coreReindex m e)).coreSlice s x).value t =ᵐ[volume]
      ((u.coreSlice s x).reindex e).value t := fun t => Eventually.of_forall (hx t)
  have hm : mass ((u.reindex (coreReindex m e)).coreSlice s x)=mass (u.coreSlice s x) := by
    rw [mass_congr_ae _ _ hv,mass_reindex]
  refine ⟨hm,?_⟩
  unfold coreConditionalObservable
  rw [potentialForm_normalized_eq,potentialForm_normalized_eq,hm,
    potentialForm_congr_values _ _ _ hv]
  congr 1
  simp only [Function.comp_apply,reindex_join_coreReindex]
  exact potentialForm_reindex _ e (fun z => W (joinConfiguration m k (x,z)))

lemma slice_positive_square_coreReindex {m q k : ℕ} (u : H1Vector (m+k))
    (e : Fin q ≃ Fin k) (W : Configuration (m+k) → ℝ) :
    sliceExpectation (u.reindex (coreReindex m e)) (fun s x =>
      (max (coreConditionalObservable (u.reindex (coreReindex m e))
        (W ∘ reindexConfiguration (coreReindex m e)) s x) 0)^2)=
    sliceExpectation u (fun s x => (max (coreConditionalObservable u W s x) 0)^2) := by
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  filter_upwards [coreConditionalObservable_coreReindex u e W s] with x hx
  rw [hx.1,hx.2]

lemma Antisymmetric.reindex {q k : ℕ} {u : H1Vector k} (hu : Antisymmetric u)
    (e : Fin q ≃ Fin k) : Antisymmetric (u.reindex e) := by
  have h : q=k := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst k
  exact hu.permutation _

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_AppendJensen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def H1Vector.appendCut {m n : ℕ} {L : Type*} [Fintype L]
    (u : H1Vector (m+n)) (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l)) (hp : ∀ z, ∑ l, χ l z^2=1)
    (D : ℝ) (hD : 0≤D) (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → L) {q k : ℕ} (e : Fin (q+k) ≃ Fin n) : H1Vector ((m+q)+k) :=
  (((u.labelCut χ hχ hp D hD hd p).reindex (coreReindex m e)).reindex (recordAssoc m q k))

theorem appendCut_positive_jensen {m n : ℕ} {L : Type*} [Fintype L]
    (u : H1Vector (m+n)) (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l)) (hp : ∀ z, ∑ l, χ l z^2=1)
    (D : ℝ) (hD : 0≤D) (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (q k : (Fin (m+n) → L) → ℕ) (e : (p : Fin (m+n) → L) → Fin (q p+k p) ≃ Fin n)
    (W : Configuration (m+n) → ℝ) (hW : Measurable W) {B : ℝ}
    (hB0 : 0≤B) (hB : ∀ x, |W x| ≤ B) :
    sliceExpectation u (fun s x => (max (coreConditionalObservable u W s x) 0)^2) ≤
      ∑ p, sliceExpectation (u.appendCut χ hχ hp D hD hd p (e p)) (fun s x =>
        (max (coreConditionalObservable (u.appendCut χ hχ hp D hD hd p (e p))
          (W ∘ reindexConfiguration (coreReindex m (e p)) ∘ reindexConfiguration (recordAssoc m (q p) (k p))) s x) 0)^2) := by
  apply (labelCut_conditional_positive_jensen u χ hχ hp D hD hd W hW hB0 hB).trans
  apply Finset.sum_le_sum
  intro p hp0
  rw [←slice_positive_square_coreReindex _ (e p) W]
  exact record_more_positive_jensen _ _
    (hW.comp (reindexConfiguration_continuous _).measurable) hB0 (fun _ => hB _)

lemma form_appendCut {J m n : ℕ} (S : Nuclei J) {L : Type*} [Fintype L]
    (u : H1Vector (m+n)) (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l)) (hp : ∀ z, ∑ l, χ l z^2=1)
    (D : ℝ) (hD : 0≤D) (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → L) {q k : ℕ} (e : Fin (q+k) ≃ Fin n) :
    form S (u.appendCut χ hχ hp D hD hd p e)=form S (u.labelCut χ hχ hp D hD hd p) := by
  simp only [H1Vector.appendCut,form_reindex]

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def PartlyAntisymmetric {n : ℕ} (u : H1Vector n) (I : Set (Fin n)) : Prop :=
  ∀ p : Equiv.Perm (Fin n), (∀ i ∉ I, p i=i) → ∀ s : Spins n,
    ∀ᵐ x, u.value (s ∘ p) (permute p x)=(((p.sign:ℤ):ℂ))*u.value s x

def coreIndexSet (m k : ℕ) : Set (Fin (m+k)) := Set.range (Fin.natAdd m : Fin k → Fin (m+k))

lemma Antisymmetric.partly {n : ℕ} {u : H1Vector n} (hu : Antisymmetric u) (I : Set (Fin n)) :
    PartlyAntisymmetric u I := fun p _ s => hu p s

lemma reindexConfiguration_measurePreserving {m n : ℕ} (e : Fin m ≃ Fin n) :
    MeasurePreserving (reindexConfiguration e) volume volume := by
  have h : m=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  exact permute_measurePreserving e.symm

lemma reindex_permute {m n : ℕ} (e : Fin m ≃ Fin n) (p : Equiv.Perm (Fin m)) (x : Configuration m) :
    reindexConfiguration e (permute p x)=permute (e.permCongr p) (reindexConfiguration e x) := by
  ext ⟨i,b⟩
  simp [reindexConfiguration,permute,Equiv.permCongr_apply]

lemma PartlyAntisymmetric.reindex {m n : ℕ} {u : H1Vector n} {I : Set (Fin n)}
    (hu : PartlyAntisymmetric u I) (e : Fin m ≃ Fin n) (K : Set (Fin m))
    (hK : ∀ i∈K, e i∈I) : PartlyAntisymmetric (u.reindex e) K := by
  intro p hp s
  have hfix : ∀ i∉I, e.permCongr p i=i := by
    intro i hi
    have he : e.symm i∉K := fun h => hi (by simpa using hK _ h)
    simp [Equiv.permCongr_apply,hp _ he]
  have H := (reindexConfiguration_measurePreserving e).quasiMeasurePreserving.ae
    (hu (e.permCongr p) hfix (s ∘ e.symm))
  filter_upwards [H] with x hx
  rw [H1Vector.reindex_value,H1Vector.reindex_value,reindex_permute]
  have hs : (s ∘ p) ∘ e.symm=(s ∘ e.symm) ∘ (e.permCongr p) := by
    funext i
    simp [Function.comp_apply,Equiv.permCongr_apply]
  rw [hs]
  simpa only [Equiv.Perm.sign_permCongr] using hx

lemma PartlyAntisymmetric.labelCut {n : ℕ} {u : H1Vector n} {I : Set (Fin n)}
    (hu : PartlyAntisymmetric u I) {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin n → L) (K : Set (Fin n)) (hKI : K⊆I) (l : L)
    (hc : ∀ i∈K, p i=l) : PartlyAntisymmetric (u.labelCut χ hχ hp D hD hd p) K := by
  intro q hq s
  have hfix : ∀ i∉I, q i=i := fun i hi => hq i (fun h => hi (hKI h))
  have hperm (i : Fin n) : p (q i)=p i := by
    by_cases hi : i∈K
    · have hqi : q i∈K := by
        by_contra hh
        have he : q i=i := q.injective (hq _ hh)
        apply hh
        rw [he]
        exact hi
      rw [hc _ hi,hc _ hqi]
    · rw [hq _ hi]
  filter_upwards [hu q hfix s] with x hx
  change (↑(tensorCut χ p (permute q x)):ℂ)*u.value (s ∘ q) (permute q x)=_
  rw [tensorCut_permute_invariant χ p q hperm,hx]
  change (↑(tensorCut χ p x):ℂ)*((((q.sign:ℤ):ℂ))*u.value s x)=
    (((q.sign:ℤ):ℂ))*((↑(tensorCut χ p x):ℂ)*u.value s x)
  ring

lemma PartlyAntisymmetric.coreSlice {m k : ℕ} {u : H1Vector (m+k)}
    (hu : PartlyAntisymmetric u (coreIndexSet m k)) (s : Spins m) :
    ∀ᵐ x, Antisymmetric (u.coreSlice s x) := by
  apply u.coreSlice_antisymmetric
  intro p t
  apply hu (corePerm m p) _ (Fin.append s t)
  intro i hi
  refine Fin.addCases (fun j hj => ?_) (fun j hj => ?_) i hi
  · exact corePerm_left m p j
  · exact (hj ⟨j,rfl⟩).elim

lemma appendCut_partlyAntisymmetric {m n : ℕ} {u : H1Vector (m+n)}
    (hu : PartlyAntisymmetric u (coreIndexSet m n)) {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → L) {q k : ℕ} (e : Fin (q+k) ≃ Fin n) (l : L)
    (hc : ∀ i : Fin k, p (Fin.natAdd m (e (Fin.natAdd q i)))=l) :
    PartlyAntisymmetric (u.appendCut χ hχ hp D hD hd p e) (coreIndexSet (m+q) k) := by
  let I : Set (Fin (m+n)) := Set.range (fun i : Fin k => Fin.natAdd m (e (Fin.natAdd q i)))
  let K : Set (Fin (m+(q+k))) := Set.range (fun i : Fin k => Fin.natAdd m (Fin.natAdd q i))
  have hI : I⊆coreIndexSet m n := by rintro i ⟨j,rfl⟩; exact ⟨_,rfl⟩
  have hcut := hu.labelCut χ hχ hp D hD hd p I hI l (by rintro i ⟨j,rfl⟩; exact hc j)
  have hsort := hcut.reindex (coreReindex m e) K (by
    rintro i ⟨j,rfl⟩
    exact ⟨j,by rw [coreReindex_right]⟩)
  exact hsort.reindex (recordAssoc m q k) (coreIndexSet (m+q) k) (by
    rintro i ⟨j,rfl⟩
    exact ⟨j,by rw [recordAssoc_right]⟩)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_Partial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def PartlySupported {n : ℕ} (u : H1Vector n) (I : Set (Fin n)) (A : Set Space) : Prop :=
  ∀ s : Spins n, ∀ᵐ x, ∀ i∈I, position x i∉A → u.value s x=0

def outIndexSet (m k : ℕ) : Set (Fin (m+k)) := Set.range (Fin.castAdd k : Fin m → Fin (m+k))

lemma position_reindex {m n : ℕ} (e : Fin m ≃ Fin n) (x : Configuration m) (i : Fin m) :
    position (reindexConfiguration e x) (e i)=position x i := by
  ext b
  simp [position,reindexConfiguration]

lemma PartlySupported.reindex {m n : ℕ} {u : H1Vector n} {I : Set (Fin n)} {A : Set Space}
    (hu : PartlySupported u I A) (e : Fin m ≃ Fin n) (K : Set (Fin m))
    (hK : ∀ i∈K, e i∈I) : PartlySupported (u.reindex e) K A := by
  intro s
  filter_upwards [(reindexConfiguration_measurePreserving e).quasiMeasurePreserving.ae (hu (s ∘ e.symm))] with x hx
  intro i hi hxA
  rw [H1Vector.reindex_value]
  exact hx (e i) (hK i hi) (by rwa [position_reindex])

lemma PartlySupported.mono_space {n : ℕ} {u : H1Vector n} {I : Set (Fin n)} {A B : Set Space}
    (hu : PartlySupported u I A) (hAB : A⊆B) : PartlySupported u I B := by
  intro s
  filter_upwards [hu s] with x hx
  exact fun i hi hh => hx i hi (fun h => hh (hAB h))

lemma PartlySupported.union {n : ℕ} {u : H1Vector n} {I K : Set (Fin n)} {A : Set Space}
    (hu : PartlySupported u I A) (hv : PartlySupported u K A) : PartlySupported u (I∪K) A := by
  intro s
  filter_upwards [hu s,hv s] with x hx hy
  intro i hi hh
  exact hi.elim (fun h => hx i h hh) (fun h => hy i h hh)

lemma PartlySupported.labelCut {n : ℕ} {u : H1Vector n} {I : Set (Fin n)} {A : Set Space}
    (hu : PartlySupported u I A) {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin n → L) : PartlySupported (u.labelCut χ hχ hp D hD hd p) I A := by
  intro s
  filter_upwards [hu s] with x hx
  intro i hi hh
  change (↑(tensorCut χ p x):ℂ)*u.value s x=0
  rw [hx i hi hh,mul_zero]

lemma labelCut_partlySupported {n : ℕ} (u : H1Vector n) {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin n → L) (I : Set (Fin n)) (l : L) (hc : ∀ i∈I, p i=l)
    (A : Set Space) (hA : ∀ z∉A, χ l z=0) :
    PartlySupported (u.labelCut χ hχ hp D hD hd p) I A := by
  intro s
  filter_upwards [] with x
  intro i hi hh
  have hzero : tensorCut χ p x=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hc i hi,hA _ hh]
  change (↑(tensorCut χ p x):ℂ)*u.value s x=0
  rw [hzero,Complex.ofReal_zero,zero_mul]

lemma PartlySupported.coreSlice {m k : ℕ} {u : H1Vector (m+k)} {A : Set Space}
    (hu : PartlySupported u (coreIndexSet m k) A) (s : Spins m) :
    ∀ᵐ x, SpatiallySupported (u.coreSlice s x) A := by
  have hall : ∀ᵐ x : Configuration m, ∀ t : Spins k, ∀ᵐ z : Configuration k,
      ∀ i∈coreIndexSet m k, position (joinConfiguration m k (x,z)) i∉A →
        u.value (Fin.append s t) (joinConfiguration m k (x,z))=0 :=
    ae_all_iff.mpr (fun t => Measure.ae_ae_of_ae_prod
      ((joinConfiguration_measurePreserving m k).quasiMeasurePreserving.ae (hu (Fin.append s t))))
  filter_upwards [u.coreSliceRegular_ae s,hall] with x hx ha
  intro t
  filter_upwards [ha t] with z hz hza
  obtain ⟨i,hi⟩ : ∃ i : Fin k, position z i∉A := by
    simpa only [allPositions,Set.mem_ofPred_eq,not_forall] using hza
  rw [u.coreSlice_value s hx]
  exact hz (Fin.natAdd m i) ⟨i,rfl⟩ (by rwa [position_join_right])

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma appendCut_coreSupported {m n : ℕ} (u : H1Vector (m+n)) {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → L) {q k : ℕ} (e : Fin (q+k) ≃ Fin n) (l : L)
    (hc : ∀ i : Fin k, p (Fin.natAdd m (e (Fin.natAdd q i)))=l)
    (A : Set Space) (hA : ∀ z∉A, χ l z=0) :
    PartlySupported (u.appendCut χ hχ hp D hD hd p e) (coreIndexSet (m+q) k) A := by
  let I : Set (Fin (m+n)) := Set.range (fun i : Fin k => Fin.natAdd m (e (Fin.natAdd q i)))
  let K : Set (Fin (m+(q+k))) := Set.range (fun i : Fin k => Fin.natAdd m (Fin.natAdd q i))
  have hcut := labelCut_partlySupported u χ hχ hp D hD hd p I l (by rintro i ⟨j,rfl⟩; exact hc j) A hA
  have hsort := hcut.reindex (coreReindex m e) K (by
    rintro i ⟨j,rfl⟩
    exact ⟨j,by rw [coreReindex_right]⟩)
  exact hsort.reindex (recordAssoc m q k) (coreIndexSet (m+q) k) (by
    rintro i ⟨j,rfl⟩
    exact ⟨j,by rw [recordAssoc_right]⟩)

lemma appendCut_outSupported {m n : ℕ} {u : H1Vector (m+n)} {A : Set Space}
    (hu : PartlySupported u (outIndexSet m n) A) {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → L) {q k : ℕ} (e : Fin (q+k) ≃ Fin n) (l : L)
    (hc : ∀ i : Fin q, p (Fin.natAdd m (e (Fin.castAdd k i)))=l)
    (B : Set Space) (hB : ∀ z∉B, χ l z=0) :
    PartlySupported (u.appendCut χ hχ hp D hD hd p e) (outIndexSet (m+q) k) (A∪B) := by
  let I : Set (Fin (m+n)) := Set.range (fun i : Fin q => Fin.natAdd m (e (Fin.castAdd k i)))
  let K : Set (Fin (m+(q+k))) := Set.range (fun i : Fin q => Fin.natAdd m (Fin.castAdd k i))
  have hnew := labelCut_partlySupported u χ hχ hp D hD hd p I l (by rintro i ⟨j,rfl⟩; exact hc j) B hB
  have hold := hu.labelCut χ hχ hp D hD hd p
  have hcut := (hold.mono_space (Set.subset_union_left : A⊆A∪B)).union
    (hnew.mono_space (Set.subset_union_right : B⊆A∪B))
  have hsort := hcut.reindex (coreReindex m e) (outIndexSet m (q+k)∪K) (by
    intro i hi
    rcases hi with ⟨j,rfl⟩|⟨j,rfl⟩
    · left
      exact ⟨j,by rw [coreReindex_left]⟩
    · right
      exact ⟨j,by rw [coreReindex_right]⟩)
  apply hsort.reindex (recordAssoc m q k) (outIndexSet (m+q) k)
  rintro i ⟨j,rfl⟩
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · left
    exact ⟨l,by rw [recordAssoc_left]⟩
  · right
    exact ⟨l,by rw [recordAssoc_middle]⟩

theorem binary_append_cut_outcome {m n : ℕ} (u : H1Vector (m+n))
    (hu : PartlyAntisymmetric u (coreIndexSet m n)) {A : Set Space}
    (hA : PartlySupported u (outIndexSet m n) A)
    (χ : Fin 2 → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → Fin 2) (B C : Set Space)
    (hB : ∀ z∉B, χ 0 z=0) (hC : ∀ z∉C, χ 1 z=0) :
    ∃ q k : ℕ, ∃ e : Fin (q+k) ≃ Fin n,
      PartlyAntisymmetric (u.appendCut χ hχ hp D hD hd p e) (coreIndexSet (m+q) k) ∧
      PartlySupported (u.appendCut χ hχ hp D hD hd p e) (coreIndexSet (m+q) k) C ∧
      PartlySupported (u.appendCut χ hχ hp D hD hd p e) (outIndexSet (m+q) k) (A∪B) := by
  obtain ⟨q,k,e,he0,he1⟩ := exists_binary_order (fun i : Fin n => p (Fin.natAdd m i))
  exact ⟨q,k,e,appendCut_partlyAntisymmetric hu χ hχ hp D hD hd p e 1 he1,
    appendCut_coreSupported u χ hχ hp D hD hd p e 1 he1 C hC,
    appendCut_outSupported hA χ hχ hp D hD hd p e 0 he0 B hB⟩

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_LocalizedEnsemble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def conditionalOutCost {J m k : ℕ} (S : Nuclei J) (ψ : H1Vector (m+k)) : ℝ :=
  outerKinetic ψ+sliceExpectation ψ (fun s x => pairPotential x-
    ∑ i : Fin m, coreScreenedField S (ψ.coreSlice s x).normalized (position x i))

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_RecordedCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma localCount_reindex {m n : ℕ} (A : Set Space) (e : Fin m ≃ Fin n) (x : Configuration m) :
    localCount A (reindexConfiguration e x)=localCount A x := by
  change (∑ i : Fin n, A.indicator (fun _ => (1:ℝ)) (position x (e.symm i)))=_
  exact Equiv.sum_comp e.symm (fun i : Fin m => A.indicator (fun _ => (1:ℝ)) (position x i))

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_RecordedEnsemble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

structure RecordedEnsemble (n : ℕ) where
  index : Type
  finite : Fintype index
  out : index → ℕ
  core : index → ℕ
  vector : (p : index) → H1Vector (out p+core p)
  labels : (p : index) → Fin (out p+core p) ≃ Fin n
attribute [instance] RecordedEnsemble.finite

namespace RecordedEnsemble
variable {n J : ℕ}

def totalMass (T : RecordedEnsemble n) : ℝ := ∑ p, mass (T.vector p)
def totalForm (T : RecordedEnsemble n) (S : Nuclei J) : ℝ := ∑ p, form S (T.vector p)
def Conserves (T : RecordedEnsemble n) (ψ : H1Vector n) : Prop :=
  ∀ W : Configuration n → ℝ, Measurable W → (∃ B : ℝ, ∀ x, |W x|≤B) →
    (∑ p, potentialForm (W ∘ reindexConfiguration (T.labels p)) (T.vector p))=potentialForm W ψ

def CoreFermionic (T : RecordedEnsemble n) : Prop :=
  ∀ p, PartlyAntisymmetric (T.vector p) (coreIndexSet (T.out p) (T.core p))
def OutSupported (T : RecordedEnsemble n) (A : Set Space) : Prop :=
  ∀ p, PartlySupported (T.vector p) (outIndexSet (T.out p) (T.core p)) A

def rawSquare (T : RecordedEnsemble n) (S : Nuclei J) (y : Space) (a : ℝ) : ℝ :=
  ∑ p, sliceExpectation (T.vector p) (fun s x =>
    (max (coreConditionalObservable (T.vector p)
      (rawSignedField (attraction S y) {z | 40*a≤‖z-y‖} y) s x) 0)^2)

lemma reindexConfiguration_trans {a b c : ℕ} (e : Fin a ≃ Fin b) (f : Fin b ≃ Fin c) :
    reindexConfiguration (e.trans f)=reindexConfiguration f ∘ reindexConfiguration e := by
  funext x
  ext ⟨i,j⟩
  rfl

lemma Conserves.population {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) {A : Set Space} (hA : MeasurableSet A) :
    (∑ p, expectedPopulation (T.vector p) A)=expectedPopulation ψ A := by
  have H := hT (localCount A) (localCount_measurable hA)
    ⟨n,fun x => by rw [abs_of_nonneg (localCount_nonneg _ _)]; exact localCount_le _ _⟩
  simpa only [Function.comp_def,localCount_reindex,potentialForm,expectedPopulation_eq _ hA] using H

end RecordedEnsemble
end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_AtomicMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def atomicCellScale (y : Space) : ℝ := ‖y‖/100000

lemma atomicCellScale_nonneg (y : Space) : 0 ≤ atomicCellScale y := div_nonneg (norm_nonneg _) (by norm_num)
lemma atomicCellScale_pos {y : Space} (hy : y≠0) : 0 < atomicCellScale y := div_pos (norm_pos_iff.mpr hy) (by norm_num)
lemma atomicCellScale_norm (y : Space) : 100000*atomicCellScale y=‖y‖ := by unfold atomicCellScale; ring

lemma atomicCellScale_comparable {y z : Space} (h : ‖z-y‖ ≤ 82*atomicCellScale y) :
    atomicCellScale y/2 ≤ atomicCellScale z ∧ atomicCellScale z ≤ 2*atomicCellScale y := by
  have h1 : ‖z‖ ≤ ‖z-y‖+‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (z-y) y
  have h2 : ‖y‖ ≤ ‖z-y‖+‖z‖ := by
    have h := norm_add_le (y-z) z
    simpa only [sub_add_cancel,norm_sub_rev y z] using h
  have hy := atomicCellScale_nonneg y
  have he := atomicCellScale_norm y
  have hz := atomicCellScale_norm z
  constructor <;> linarith

lemma atomicCellScale_near_nonzero {y z : Space} (hy : y≠0)
    (h : ‖z-y‖ ≤ 82*atomicCellScale y) : z≠0 := by
  have hp := atomicCellScale_pos hy
  have H := (atomicCellScale_comparable h).1
  intro hz
  subst z
  have hzero : atomicCellScale (0:Space)=0 := by norm_num [atomicCellScale]
  rw [hzero] at H
  linarith

lemma exists_atomic_patch_mesh : ∃ t : Finset Space,
    (∀ z∈t, ‖z‖ ≤ 80) ∧ (∀ w : Space, ‖w‖ ≤ 80 → ∃ z∈t, ‖w-z‖ < 1/4) := by
  let B := Metric.closedBall (0:Space) 80
  have hc : IsCompact B := isCompact_closedBall _ _
  have hcover : B ⊆ ⋃ z : B, Metric.ball z.val (1/4) := by
    intro w hw
    exact Set.mem_iUnion.mpr ⟨⟨w,hw⟩,by simp⟩
  obtain ⟨t,ht⟩ := hc.elim_finite_subcover (fun z : B => Metric.ball z.val (1/4))
    (fun _ => Metric.isOpen_ball) hcover
  refine ⟨t.image Subtype.val,?_,?_⟩
  · intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    simpa only [B,Metric.mem_closedBall,dist_zero_right] using v.property
  · intro w hw
    have hwB : w∈B := by simpa only [B,Metric.mem_closedBall,dist_zero_right] using hw
    obtain ⟨z,hz⟩ := Set.mem_iUnion.mp (ht hwB)
    obtain ⟨hzt,hzw⟩ := Set.mem_iUnion.mp hz
    refine ⟨z.val,Finset.mem_image.mpr ⟨z,hzt,rfl⟩,?_⟩
    simpa only [Metric.mem_ball,dist_eq_norm] using hzw

def atomicPatchMesh : Finset Space := Classical.choose exists_atomic_patch_mesh
lemma atomicPatchMesh_norm (z : Space) (hz : z∈atomicPatchMesh) : ‖z‖ ≤ 80 :=
  (Classical.choose_spec exists_atomic_patch_mesh).1 z hz

def atomicMeshCenter (y z : Space) : Space := y+atomicCellScale y • z

lemma atomicMeshCenter_distance (y z : Space) (hz : z∈atomicPatchMesh) :
    ‖atomicMeshCenter y z-y‖ ≤ 80*atomicCellScale y := by
  simp only [atomicMeshCenter,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg (atomicCellScale_nonneg y)]
  nlinarith [atomicPatchMesh_norm z hz,atomicCellScale_nonneg y]

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_AtomicHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def atomicIMS {n : ℕ} (ψ : H1Vector n) (y : Space) : ℝ :=
  3*(radialCutCoefficient/(40*atomicCellScale y))^2*
    expectedPopulation ψ (Metric.closedBall y (80*atomicCellScale y))

def atomicPatchRegion {j : ℕ} (y : Fin j → Space) : Set Space :=
  ⋃ i, Metric.closedBall (y i) (80*atomicCellScale (y i))

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_AtomicBudgetHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

structure AtomicBudgetHistory {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (B : ℝ) (j : ℕ) where
  ensemble : RecordedEnsemble n
  target : Fin j → Space
  nonzero : ∀ i, target i≠0
  law : ensemble.Conserves ψ
  fermionic : ensemble.CoreFermionic
  support : ensemble.OutSupported (atomicPatchRegion target)
  mass_eq : ensemble.totalMass=mass ψ
  energy : ensemble.totalForm S≤form S ψ+B+∑ i, atomicIMS ψ (target i)

namespace AtomicBudgetHistory
variable {J n j : ℕ} {S : Nuclei J} {ψ : H1Vector n} {B : ℝ}

def center (T : AtomicBudgetHistory S ψ B j) (c : Fin j × {z : Space // z∈atomicPatchMesh}) : Space :=
  atomicMeshCenter (T.target c.1) c.2.val

lemma center_nonzero (T : AtomicBudgetHistory S ψ B j) (c) : T.center c≠0 :=
  atomicCellScale_near_nonzero (T.nonzero c.1) (by
    change ‖atomicMeshCenter (T.target c.1) c.2.val-T.target c.1‖≤_
    have H := atomicMeshCenter_distance (T.target c.1) c.2.val c.2.property
    nlinarith [atomicCellScale_nonneg (T.target c.1)])

end AtomicBudgetHistory
end Coulomb
end

end
end

end OAI
end


