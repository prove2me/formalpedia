-- Prove2me | Definitions.Def_OAIQ039C038
-- name    : OAIQ039C038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:22:59.801344+00:00
-- url     : https://prove2.me/theorems/488b965a-1a7d-4cbf-968d-ed0e4dfee3fc
-- title:
--   Definitions bundle OAIQ039C038 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 12 definitions and 18 theorems. The definitions and types are `OAI.Kadison.InfiniteAmplification.flatten`, `OAI.Kadison.InfiniteAmplification.reindex`, `OAI.Kadison.InfiniteAmplification.stableEmbedding`, `OAI.Kadison.IrreducibleTowerAveraging.eventualFiber`, `OAI.Kadison.IrreducibleTowerAveraging.orbit`, `OAI.Kadison.IrreducibleTowerAveraging.stageUnitaries`, `OAI.Kadison.MatrixCornerExtension.extend`, `OAI.Kadison.Polar.binaryRemainder`, `OAI.Kadison.Polar.dyadicRemainder`, `OAI.Kadison.Polar.dyadicStep`, `OAI.Kadison.Polar.halfCut`, `OAI.Kadison.RelativeMatrix.concrete`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_DyadicSpectral`, `Commutator_InfiniteReindex`, `Commutator_IrreducibleTowerAveraging`, `Commutator_MatrixCornerExtension`, `Commutator_MatrixModules`, `Commutator_PolarSupport`, `Commutator_ProjectionPartition`, `Commutator_RelativeMatrix`, `Commutator_SpectralCutoff`, `Commutator_StableGNSModule`.
--
--   **Imports.** It imports the bundles `OAIQ039C022`, `OAIQ039C024`, `OAIQ039C027` and `OAIQ039C028` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C048`, `OAIQ039C049` and `OAIQ039C052`; the statements `OAI.Kadison.IrreducibleTowerAveraging.hull_bounded`, `OAI.Kadison.IrreducibleTowerAveraging.hull_trace`, `OAI.Kadison.IrreducibleTowerAveraging.orbit_subset_eventualFiber`, `OAI.Kadison.IrreducibleTowerAveraging.scalar_mem_hull`, `OAI.Kadison.MatrixCornerExtension.extend_intertwines` and `OAI.Kadison.MatrixCornerExtension.norm_sub_extend_le`; the proofs of `OAI.Kadison.CentralSpectral.separable_uniform_bound`, `OAI.Kadison.IrreducibleTowerAveraging.expectation_tendsto`, `OAI.Kadison.IrreducibleTowerAveraging.hull_bounded`, `OAI.Kadison.IrreducibleTowerAveraging.hull_trace`, `OAI.Kadison.IrreducibleTowerAveraging.orbit_subset_eventualFiber`, `OAI.Kadison.IrreducibleTowerAveraging.scalar_mem_hull`, `OAI.Kadison.MatrixCornerExtension.extend_intertwines`, `OAI.Kadison.MatrixCornerExtension.norm_sub_extend_le`, `OAI.Kadison.NormalRepresentation.exists_stable_gns_model`, `OAI.Kadison.PositiveWOT.positive_strong_null` and `OAI.Kadison.PositiveWOT.threshold_exhaustion`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C024
import Definitions.Def_OAIQ039C027
import Definitions.Def_OAIQ039C028

section
-- module Solutions.OAIQ039_CM.Commutator_PolarSupport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma rightSupport_mem (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T∈M) :
    rightSupport T∈M := by
  rw [rightSupport,←partialIsometry_initial]
  exact M.mul_mem (M.star_mem' (partialIsometry_mem_vonNeumann M hT)) (partialIsometry_mem_vonNeumann M hT)

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SpectralCutoff
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma partialIsometry_of_nonneg {T : H →L[ℂ] H} (hT : 0≤T) :
    partialIsometry T=rightSupport T := by
  have h : ∀ x : initial T, initialMap T x=(x : H) := by
    intro x
    refine (absToInitial_dense T).induction_on x
      (isClosed_eq (initialMap T).continuous continuous_subtype_val) ?_
    intro y
    rw [initialMap_abs]
    change T y=CFC.abs T y
    rw [CFC.abs_of_nonneg T hT]
  ext x
  exact h ((initial T).orthogonalProjectionOnto x)

lemma mul_rightSupport_eq_zero_of_nonneg {T B : H →L[ℂ] H} (hT : 0≤T)
    (hBT : B*T=0) : B*rightSupport T=0 := by
  have h : ∀ x : initial T, B x=0 := by
    intro x
    refine (absToInitial_dense T).induction_on x
      (isClosed_eq (B.continuous.comp continuous_subtype_val) continuous_const) ?_
    intro y
    change B (CFC.abs T y)=0
    rw [CFC.abs_of_nonneg T hT]
    exact congrArg (fun R : H →L[ℂ] H => R y) hBT
  ext x
  exact h ((initial T).orthogonalProjectionOnto x)

lemma rightSupport_mul_eq_zero_of_nonneg {T B : H →L[ℂ] H} (hT : 0≤T)
    (hTB : T*B=0) : rightSupport T*B=0 := by
  have hs : star B*T=0 := by
    simpa only [star_mul,(IsSelfAdjoint.of_nonneg hT).star_eq,star_zero] using congrArg star hTB
  simpa only [star_mul,star_star,(isProjection_rightSupport T).isSelfAdjoint.star_eq,star_zero] using
    congrArg star (mul_rightSupport_eq_zero_of_nonneg hT hs)

def halfCut (T : H →L[ℂ] H) : H →L[ℂ] H :=
  rightSupport (T+T-(1 : H →L[ℂ] H))⁺

lemma isProjection_halfCut (T : H →L[ℂ] H) : IsStarProjection (halfCut T) :=
  isProjection_rightSupport _

lemma halfCut_mem (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T∈M) : halfCut T∈M := by
  apply rightSupport_mem M
  apply posPart_mem M
  exact M.toStarSubalgebra.sub_mem (M.add_mem hT hT) M.one_mem

lemma halfCut_commute {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) : Commute (halfCut T) T := by
  let b := T+T-(1 : H →L[ℂ] H)
  have hb : Commute b T := ((Commute.refl T).add_left (Commute.refl T)).sub_left (Commute.one_left T)
  have hbp : Commute b⁺ T := hb.cfcₙ_real (·⁺)
  have hs : Commute b⁺ (star T) := by rwa [hT.star_eq]
  change Commute (rightSupport b⁺) T
  simpa only [partialIsometry_of_nonneg (CFC.posPart_nonneg b)] using partialIsometry_commutes b⁺ T hbp hs

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DyadicSpectral
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology BigOperators

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def binaryRemainder (T : H →L[ℂ] H) : H →L[ℂ] H := T+T-halfCut T

lemma halfCut_commutes {T A : H →L[ℂ] H} (hTA : Commute T A) (hTAstar : Commute T (star A)) :
    Commute (halfCut T) A := by
  let b := T+T-1
  have hb : Commute b A := (hTA.add_left hTA).sub_left (Commute.one_left A)
  have hbs : Commute b (star A) := (hTAstar.add_left hTAstar).sub_left (Commute.one_left (star A))
  change Commute (rightSupport b⁺) A
  simpa only [partialIsometry_of_nonneg (CFC.posPart_nonneg b)] using
    partialIsometry_commutes b⁺ A (hb.cfcₙ_real (·⁺)) (hbs.cfcₙ_real (·⁺))

def dyadicRemainder (T : H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => T
  | n+1 => binaryRemainder (dyadicRemainder T n)

lemma dyadicRemainder_mem (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T∈M) (n : ℕ) :
    dyadicRemainder T n∈M := by
  induction n with
  | zero => exact hT
  | succ n ih => exact M.toStarSubalgebra.sub_mem (M.add_mem ih ih) (halfCut_mem M ih)

def dyadicStep (T : H →L[ℂ] H) (n : ℕ) : H →L[ℂ] H :=
  ∑ i∈Finset.range n, ((2:ℝ)⁻¹^(i+1)) • halfCut (dyadicRemainder T i)

lemma dyadicStep_remainder (T : H →L[ℂ] H) (n : ℕ) :
    T-dyadicStep T n=((2:ℝ)⁻¹^n) • dyadicRemainder T n := by
  induction n with
  | zero => simp [dyadicStep,dyadicRemainder]
  | succ n ih =>
    rw [dyadicStep,Finset.sum_range_succ]
    rw [←dyadicStep]
    change T-(dyadicStep T n+_)=_
    rw [sub_add_eq_sub_sub,ih]
    simp only [dyadicRemainder,binaryRemainder,smul_sub,smul_add,pow_succ]
    module

lemma dyadicRemainder_commutes {T A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    (hTA : Commute T A) (n : ℕ) : Commute (dyadicRemainder T n) A := by
  induction n with
  | zero => exact hTA
  | succ n ih =>
    exact (ih.add_left ih).sub_left (halfCut_commutes ih (by simpa only [hA.star_eq] using ih))

lemma dyadicCut_commutes_original {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (n : ℕ) :
    Commute (halfCut (dyadicRemainder T n)) T := by
  have hc := dyadicRemainder_commutes hT (Commute.refl T) n
  exact halfCut_commutes hc (by simpa only [hT.star_eq] using hc)

lemma dyadicCuts_commute {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (n m : ℕ) :
    Commute (halfCut (dyadicRemainder T n)) (halfCut (dyadicRemainder T m)) := by
  have hp : IsSelfAdjoint (halfCut (dyadicRemainder T m)) :=
    (isProjection_halfCut _).isSelfAdjoint
  have hc := dyadicRemainder_commutes hp (dyadicCut_commutes_original hT m).symm n
  exact halfCut_commutes hc (by simpa only [hp.star_eq] using hc)

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InfiniteReindex
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace ENNReal

namespace Kadison.InfiniteAmplification

variable {ι κ : Type*}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def reindex (e : ι ↪ κ) : Space ι H →ₗᵢ[ℂ] Space κ H where
  toFun x := ⟨Function.extend e x 0,reindex_mem e x⟩
  map_add' x y := by
    classical
    ext k
    by_cases hk : k∈Set.range e
    · obtain ⟨i,rfl⟩ := hk
      simp only [e.injective.extend_apply,lp.coeFn_add,Pi.add_apply]
    · simp only [lp.coeFn_add,Pi.add_apply,Function.extend_apply' _ _ _ hk,Pi.zero_apply,add_zero]
  map_smul' c x := by
    classical
    ext k
    by_cases hk : k∈Set.range e
    · obtain ⟨i,rfl⟩ := hk
      simp only [e.injective.extend_apply,lp.coeFn_smul,Pi.smul_apply,RingHom.id_apply]
    · simp only [lp.coeFn_smul,Pi.smul_apply,Function.extend_apply' _ _ _ hk,Pi.zero_apply,smul_zero]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq,norm_sq]
    change (∑' k,‖Function.extend e x 0 k‖^2)=∑' i,‖x i‖^2
    simp only [extend_sq]
    exact tsum_extend_zero e.injective (fun i => ‖x i‖^2)

omit [CompleteSpace H] in
@[simp] lemma reindex_apply (e : ι ↪ κ) (x : Space ι H) (i : ι) : reindex e x (e i)=x i :=
  e.injective.extend_apply _ _ _

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma flatten_mem (x : Space ι (Space κ H)) : Memℓp (fun p : ι×κ => x p.1 p.2) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mpr
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  apply (summable_prod_of_nonneg (fun p => sq_nonneg ‖x p.1 p.2‖)).mpr
  constructor
  · intro i
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (lp.memℓp (x i)).summable
      (by norm_num : 0<(2:ℝ≥0∞).toReal)
  · simp only [←norm_sq]
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (lp.memℓp x).summable
      (by norm_num : 0<(2:ℝ≥0∞).toReal)

def flatten : Space ι (Space κ H) →ₗᵢ[ℂ] Space (ι×κ) H where
  toFun x := ⟨fun p => x p.1 p.2,flatten_mem x⟩
  map_add' x y := by ext p; rfl
  map_smul' c x := by ext p; rfl
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq,norm_sq]
    have hs : Summable (fun p : ι×κ => ‖x p.1 p.2‖^2) := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (flatten_mem x).summable
        (by norm_num : 0<(2:ℝ≥0∞).toReal)
    change (∑' p : ι×κ,‖x p.1 p.2‖^2)=∑' i,‖x i‖^2
    rw [hs.tsum_prod]
    exact tsum_congr (fun i => (norm_sq (x i)).symm)

omit [CompleteSpace H] in
@[simp] lemma flatten_apply (x : Space ι (Space κ H)) (p : ι×κ) : flatten x p=x p.1 p.2 := rfl

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_IrreducibleTowerAveraging
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.IrreducibleTowerAveraging

open TracialGNS NormalGNS MatrixExpectation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
  [∀ n, Nonempty (ι n)]

variable (stage : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ}, n ≤ m → (stage n).range ≤ (stage m).range)

def stageUnitaries : Submonoid (unitary M) where
  carrier := {u | ∃ n, (u:M) ∈ (stage n).range}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro u v ⟨n,hn⟩ ⟨m,hm⟩
    exact ⟨max n m, (stage (max n m)).range.mul_mem
      (hmono (Nat.le_max_left _ _) hn) (hmono (Nat.le_max_right _ _) hm)⟩

def orbit (a : M) : Set τ.GNS :=
  Set.range (fun u : stageUnitaries M stage hmono =>
    algebraVector τ ((u.val:M)*a*star (u.val:M)))

def eventualFiber (a : M) : Set τ.GNS :=
  {v | ∃ b : M, algebraVector τ b=v ∧ ∀ᶠ n in atTop,
    algebraVector τ (expectation (stage n) b)=algebraVector τ (expectation (stage n) a)}

end Kadison.IrreducibleTowerAveraging

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCornerExtension
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.MatrixCornerExtension

open MatrixCornerHilbert

variable {A K H ι : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

variable (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

variable {p : A} (hp : IsStarProjection p) (v : ι → A)
  (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
  (hinit : ∀ i, p*star (v i)=star (v i))
  (htotal : ∑ i, v i*star (v i)=1)

def extend (T : fixedSpace (σ p) →L[ℂ] fixedSpace (ρ p)) : K →L[ℂ] H :=
  HilbertModuleExtension.extend (columns σ v hcol) (columns ρ v hcol)
    (columns_total σ v hcol hinit htotal) (columns_total ρ v hcol hinit htotal) T

end Kadison.MatrixCornerExtension

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixModules
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.MatrixModules

open Matrix

variable {𝕜 I E : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]
  [AddCommGroup E] [Module 𝕜 E]

variable (ρ : Matrix I I 𝕜 →ₐ[𝕜] Module.End 𝕜 E) (o : I)

lemma coordinates_recombine (x : I → corner ρ o) (i : I) :
    coordinates ρ o i (recombine ρ o x) = x i := by
  apply Subtype.ext
  rw [coordinates_apply, recombine_apply, map_sum]
  have hdiag : ρ (single o i 1) (ρ (single i o 1) (x i : E)) = x i := by
    change (ρ (single o i 1) * ρ (single i o 1)) (x i : E) = _
    rw [← map_mul, Matrix.single_mul_single_same, one_mul]
    exact corner_fixed ρ o _
  rw [Finset.sum_eq_single i]
  · exact hdiag
  · intro j _ hji
    change (ρ (single o i 1) * ρ (single j o 1)) (x j : E) = 0
    rw [← map_mul, Matrix.single_mul_single_of_ne 1 o i j hji.symm 1,
      map_zero, LinearMap.zero_apply]
  · simp

end Kadison.MatrixModules
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionPartition
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.SpectralPartition

variable {R : Type*} [Ring R] [StarRing R]

theorem exists_partition (n : ℕ) (p : Fin n → R)
    (hp : ∀ i,IsStarProjection (p i)) (hc : ∀ i j,Commute (p i) (p j)) :
    ∃ (J : Type) (_ : Fintype J) (e : J → R),
      (∀ j,IsStarProjection (e j)) ∧
      (∀ j k,j≠k → e j*e k=0) ∧
      (∑ j,e j)=1 ∧
      (∀ i,∃ χ : J → Bool,p i=∑ j,if χ j then e j else 0) ∧
      (∀ a : R,(∀ i,Commute a (p i)) → ∀ j,Commute a (e j)) := by
  classical
  induction n with
  | zero =>
    refine ⟨Unit,inferInstance,fun _ => 1,fun _ => IsStarProjection.one R,?_,?_,?_,?_⟩
    · intro j k h; exact (h (Subsingleton.elim _ _)).elim
    · simp
    · intro i; exact Fin.elim0 i
    · intro a h j; exact Commute.one_right a
  | succ n ih =>
    obtain ⟨J,hJ,e,he,ho,hs,hr,ha⟩ := ih (fun i => p i.succ)
      (fun i => hp i.succ) (fun i j => hc i.succ j.succ)
    let : Fintype J := hJ
    have hpe (j : J) : Commute (p 0) (e j) := ha (p 0) (fun i => hc 0 i.succ) j
    let f : Bool × J → R := fun j => splitPiece (p 0) j.1*e j.2
    refine ⟨Bool×J,inferInstance,f,?_,?_,?_,?_,?_⟩
    · intro j
      exact (splitPiece_projection (hp 0) j.1).mul (he j.2)
        (splitPiece_commute (hpe j.2).symm j.1).symm
    · rintro ⟨b,j⟩ ⟨c,k⟩ h
      change (splitPiece (p 0) b*e j)*(splitPiece (p 0) c*e k)=0
      rw [swap_middle _ _ _ _ (splitPiece_commute (hpe j).symm c)]
      by_cases hj : j=k
      · have hbc : b≠c := fun hb => h (Prod.ext hb hj)
        rw [splitPiece_orthogonal (hp 0) hbc,zero_mul]
      · rw [ho j k hj,mul_zero]
    · change (∑ j : Bool×J,splitPiece (p 0) j.1*e j.2)=1
      rw [Fintype.sum_prod_type]
      simp only [←Finset.mul_sum,hs,mul_one]
      exact splitPiece_sum _
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · refine ⟨fun j => j.1,?_⟩
        change p 0=∑ j : Bool×J,if j.1 then splitPiece (p 0) j.1*e j.2 else 0
        rw [Fintype.sum_prod_type,Fintype.sum_bool]
        simp only [Bool.false_eq_true,↓reduceIte,Finset.sum_const_zero,add_zero,splitPiece]
        rw [←Finset.mul_sum,hs,mul_one]
      · obtain ⟨χ,hχ⟩ := hr i
        refine ⟨fun j => χ j.2,?_⟩
        change p i.succ=∑ j : Bool×J,if χ j.2 then splitPiece (p 0) j.1*e j.2 else 0
        rw [Fintype.sum_prod_type,Fintype.sum_bool]
        simp only [splitPiece,↓reduceIte]
        rw [←Finset.sum_add_distrib,hχ]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hh : χ j=true
        · simp only [hh,Bool.false_eq_true,↓reduceIte,←add_mul]
          have hz : p 0+(1-p 0)=1 := by abel
          rw [hz,one_mul]
        · simp [hh]
    · intro a h j
      exact (splitPiece_commute (h 0) j.1).mul_right
        (ha a (fun i => h i.succ) j.2)

end Kadison.SpectralPartition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RelativeMatrix
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder

namespace Kadison.RelativeMatrix

open Matrix

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype I] [DecidableEq I]

variable (M : VonNeumannAlgebra H) (φ : Matrix I I ℂ →⋆ₐ[ℂ] M)

abbrev concrete : Matrix I I ℂ →⋆ₐ[ℂ] (H →L[ℂ] H) := M.toStarSubalgebra.subtype.comp φ

end Kadison.RelativeMatrix

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StableGNSModule
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison
namespace InfiniteAmplification

variable {ι H G : Type*} [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def stableEmbedding (V : H →ₗᵢ[ℂ] Space ι G) : Space ℕ H →ₗᵢ[ℂ] Space ℕ G :=
  letI := Encodable.ofCountable (ℕ×ι)
  (reindex (Encodable.encode' (ℕ×ι))).comp (flatten.comp (mapIsometry V))

end InfiniteAmplification

end Kadison

end

end
end

end OAI
end


