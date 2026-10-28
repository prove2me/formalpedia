-- Prove2me | Definitions.Def_OAIQ039C032
-- name    : OAIQ039C032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:18:48.119287+00:00
-- url     : https://prove2.me/theorems/638fa312-8b04-4cae-bd8b-df50315b097d
-- title:
--   Definitions bundle OAIQ039C032 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 6 definitions and 27 theorems. The definitions and types are `OAI.Kadison.ConcreteCorner.Space`, `OAI.Kadison.ConcreteCorner.lift`, `OAI.Kadison.ConcreteCorner.project`, `OAI.Kadison.ConcreteCorner.representation`, `OAI.Kadison.DihedralCorner.cosine`, `OAI.Kadison.TracialGNS.conjugation`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_ConcreteCornerVonNeumann`, `Commutator_HankelAlgebra`, `Commutator_KaplanskyDensity`, `Commutator_KaplanskyRange`, `Commutator_KaplanskyRational`, `Commutator_NormalGNS`, `Commutator_TracialCommutation`, `Commutator_TracialConjugation`, `Commutator_TracialDevelopment`, `Commutator_TracialRightClosure`.
--
--   **Imports.** It imports the bundles `OAIQ039C020`, `OAIQ039C021` and `OAIQ039C022` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C042`, `OAIQ039C044`, `OAIQ039C045`, `OAIQ039C047`, `OAIQ039C048`, `OAIQ039C049`, `OAIQ039C051` and `OAIQ039C052`; the statements `OAI.Kadison.ConcreteCorner.representation_injective`, `OAI.Kadison.MatrixCornerImplementation.corner_derivation_bound` and `OAI.Kadison.NormalRelativeCommutant.commutes_of_fixed`; the proofs of `OAI.Kadison.ConcreteCorner.representation_injective`, `OAI.Kadison.FaithfulNormalFunctional.gnsEmbedding_intertwines`, `OAI.Kadison.IrreducibleTowerAveraging.expectation_tendsto`, `OAI.Kadison.IrreducibleTowerAveraging.hull_trace`, `OAI.Kadison.IrreducibleTowerAveraging.orbit_subset_eventualFiber`, `OAI.Kadison.IrreducibleTowerAveraging.scalar_mem_hull`, `OAI.Kadison.LocalQuantization.exists_centered_compression`, `OAI.Kadison.NormalRelativeCommutant.commutes_of_fixed` and `OAI.Kadison.TracialGNS.exists_corner_weak_zero`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C020
import Definitions.Def_OAIQ039C021
import Definitions.Def_OAIQ039C022

section
-- module Solutions.OAIQ039_CM.Commutator_ConcreteCornerVonNeumann
attribute [-instance] _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.ConcreteCorner

open MatrixCornerHilbert ReducingRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

@[simp] lemma inclusion_apply (a : Algebra M) : inclusion M a=(a:H →L[ℂ] H) := rfl

variable {M} {p : Algebra M} (hp : IsStarProjection p)

abbrev Space (_hp : IsStarProjection p) := fixedSpace (inclusion M p)

abbrev representation := corner (inclusion M) hp

abbrev project : H →L[ℂ] Space hp := cornerProjection (inclusion M) hp

@[simp] lemma project_apply (x : H) : (project hp x:H)=(p:H →L[ℂ] H) x := rfl

def lift (T : Space hp →L[ℂ] Space hp) : H →L[ℂ] H :=
  (fixedSpace (inclusion M p)).subtypeL.comp (T.comp (project hp))

@[simp] lemma lift_apply (T : Space hp →L[ℂ] Space hp) (x : H) :
    lift hp T x=(T (project hp x):H) := rfl

@[simp] lemma project_fixed (x : Space hp) : project hp (x:H)=x :=
  cornerProjection_fixed (inclusion M) hp x

lemma lift_left (T : Space hp →L[ℂ] Space hp) : (p:H →L[ℂ] H)*lift hp T=lift hp T := by
  ext x
  exact fixed_apply _ _

end Kadison.ConcreteCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HankelAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.DihedralCorner

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

variable (u d : unitary A)

@[simp] lemma wave_star (n : ℤ) : star (wave u n)=wave u (-n) := by
  rw [wave, wave, zpow_neg, ←Unitary.star_eq_inv, Unitary.coe_star]

variable (hr : MulAut.conj d u=u⁻¹)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2 : ℂ) • (1+(d : A)))

def cosine (n : ℤ) : Corner hp :=
  ⟨p*wave u n*p, by constructor <;> simp [mul_assoc, ←mul_assoc p p, hp.isIdempotentElem.eq]⟩

@[simp] lemma cosine_coe (n : ℤ) : ((cosine u hp n : Corner hp) : A)=p*wave u n*p := rfl

end Kadison.DihedralCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyRational
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

namespace Kadison.Kaplansky

variable {A : Type*} [CStarAlgebra A]

lemma kernel_norm_le (a : A) : ‖kernel a‖≤1 :=
  norm_cfc_le (by norm_num) (fun t _ => rationalKernel_bound t)

lemma kernel_den {a : A} (ha : IsSelfAdjoint a) : kernel a*(1+a*a)=1 := by
  have hden : cfc (fun t : ℝ => 1+t^2) a=1+a*a := by
    rw [cfc_const_add (1:ℝ) (fun t => t^2) a (continuous_id.pow 2).continuousOn ha,
      cfc_pow_id a 2 ha,pow_two,map_one]
  rw [←hden, kernel,←cfc_mul rationalKernel (fun t : ℝ => 1+t^2) a
    continuous_rationalKernel.continuousOn (continuous_const.add (continuous_id.pow 2)).continuousOn]
  have he : (fun t : ℝ => rationalKernel t*(1+t^2))=(fun _ => 1) := by
    funext t
    exact inv_mul_cancel₀ (ne_of_gt (denom_pos t))
  rw [he,cfc_const_one ℝ a ha]

lemma den_kernel {a : A} (ha : IsSelfAdjoint a) : (1+a*a)*kernel a=1 := by
  have h := congrArg star (kernel_den ha)
  simpa only [star_mul,star_add,star_one,ha.star_eq,(kernel_selfAdjoint a).star_eq] using h

lemma clip_difference {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    clip a-clip b=(2:ℝ) • (kernel a*(a-b)*kernel b)-
      clip a*(a-b)*b*kernel b := by
  have hka := kernel_commute ha
  have hab : a*kernel a-b*kernel b=
      kernel a*(a-b)*kernel b-a*kernel a*(a-b)*b*kernel b := by
    calc
      a*kernel a-b*kernel b =
        a*kernel a*((1+b*b)*kernel b)-(kernel a*(1+a*a))*b*kernel b := by
          rw [den_kernel hb,kernel_den ha,mul_one,one_mul]
      _ = _ := by noncomm_ring [hka.eq]
  rw [clip_formula ha,clip_formula hb,←smul_sub,hab,smul_sub]
  simp only [smul_mul_assoc]

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyDensity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.Kaplansky

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma clip_difference_apply {a b : H →L[ℂ] H} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (x : H) :
    ‖clip a x-clip b x‖≤2*‖(a-b) (kernel b x)‖+‖(a-b) (b (kernel b x))‖ := by
  rw [←sub_apply,clip_difference ha hb]
  simp only [sub_apply,smul_apply,mul_apply_eq_comp]
  calc
    ‖(2:ℝ) • (kernel a ((a-b) (kernel b x)))-clip a ((a-b) (b (kernel b x)))‖
      ≤‖(2:ℝ) • (kernel a ((a-b) (kernel b x)))‖+
        ‖clip a ((a-b) (b (kernel b x)))‖ := norm_sub_le _ _
    _≤2*‖(a-b) (kernel b x)‖+‖(a-b) (b (kernel b x))‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (contraction_apply (kernel_norm_le a) _) (by norm_num))
        (contraction_apply (clip_norm_le a) _)

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyRange
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace CStarAlgebra ComplexStarModule

namespace Kadison.Kaplansky

open OperatorAmplification ComplexStarModule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem selfAdjoint_contraction_finite_approx_of_clip
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hclip : ∀ a∈S, IsSelfAdjoint a → clip a∈S)
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hsT : IsSelfAdjoint T) (hnT : ‖T‖≤1) (x : ι → H) (ε : ℝ) (hε : 0<ε) :
    ∃ a : H →L[ℂ] H, a∈S ∧ IsSelfAdjoint a ∧ ‖a‖≤1 ∧ ∀ i, ‖a (x i)-T (x i)‖<ε := by
  let b := lift T
  have hb : b∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) :=
    cfc_bicommutant S hT rationalLift
  have hsb : IsSelfAdjoint b := lift_selfAdjoint T
  have hcb : clip b=T := clip_lift hsT hnT
  let v : SumSpace (H:=H) (ι⊕ι) := WithLp.toLp 2
    (Sum.elim (fun i => kernel b (x i)) (fun i => b (kernel b (x i))))
  obtain ⟨a,ha,hsa,he⟩ := selfAdjoint_finite_approx (ι⊕ι) S hb hsb v (ε/3) (by positivity)
  refine ⟨clip a,?_,clip_selfAdjoint a,clip_norm_le a,?_⟩
  · exact hclip a ha hsa
  · intro i
    have h₁ : ‖(a-b) (kernel b (x i))‖<ε/3 := by
      have h := (PiLp.norm_apply_le (p:=2)
        (diagonal (H:=H) (ι⊕ι) a v-diagonal (H:=H) (ι⊕ι) b v) (Sum.inl i)).trans_lt he
      simpa only [PiLp.sub_apply,diagonal_apply,v,WithLp.ofLp_toLp,
        Sum.elim_inl,sub_apply] using h
    have h₂ : ‖(a-b) (b (kernel b (x i)))‖<ε/3 := by
      have h := (PiLp.norm_apply_le (p:=2)
        (diagonal (H:=H) (ι⊕ι) a v-diagonal (H:=H) (ι⊕ι) b v) (Sum.inr i)).trans_lt he
      simpa only [PiLp.sub_apply,diagonal_apply,v,WithLp.ofLp_toLp,
        Sum.elim_inr,sub_apply] using h
    rw [←hcb]
    exact (clip_difference_apply hsa hsb (x i)).trans_lt (by linarith)

variable {A : Type*} [CStarAlgebra A]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

theorem range_selfAdjoint_contraction_finite_approx
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (φ.range : Set (H →L[ℂ] H))))
    (hsT : IsSelfAdjoint T) (hnT : ‖T‖≤1) (x : ι → H) (ε : ℝ) (hε : 0<ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖≤1 ∧ ∀ i, ‖φ a (x i)-T (x i)‖<ε := by
  obtain ⟨b,hb,hsb,hnb,he⟩ := selfAdjoint_contraction_finite_approx_of_clip ι φ.range
    (fun _ hr hs => clip_mem_range φ hs hr) hT hsT hnT x ε hε
  obtain ⟨a,hsa,hna,ha⟩ := CStarRangeLifts.selfAdjoint_contraction φ hsb hnb hb
  exact ⟨a,hsa,hna,by simpa only [ha] using he⟩

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialDevelopment
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison

namespace TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

lemma rightMul_one : rightMul τ hτ 1 = 1 := by
  ext x
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x => simp

lemma left_right_commute (a b : A) :
    τ.gnsStarAlgHom a * rightMul τ hτ b = rightMul τ hτ b * τ.gnsStarAlgHom a := by
  ext x
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x => simp [mul_apply_eq_comp, PositiveLinearMap.gnsStarAlgHom,
      PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe, mul_assoc]

lemma rightMul_star (a : A) : rightMul τ hτ (star a) = (rightMul τ hτ a).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    simp only [rightMul_coe, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS, star_mul, star_star]
    rw [mul_assoc, hτ, mul_assoc]

lemma right_vacuum (a : A) : rightMul τ hτ a (vacuum τ) = (τ.toPreGNS a : τ.GNS) := by
  simp [vacuum]

end TracialGNS

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialConjugation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

lemma rightMul_mem_unitary (u : unitary A) :
    rightMul τ hτ (u : A) ∈ unitary (τ.GNS →L[ℂ] τ.GNS) := by
  rw [Unitary.mem_iff]
  constructor
  · change (rightMul τ hτ (u : A)).adjoint * rightMul τ hτ (u : A) = 1
    rw [← rightMul_star, ← rightMul_mul, Unitary.mul_star_self_of_mem u.property, rightMul_one]
  · change rightMul τ hτ (u : A) * (rightMul τ hτ (u : A)).adjoint = 1
    rw [← rightMul_star, ← rightMul_mul, Unitary.coe_star_mul_self, rightMul_one]

noncomputable def conjugation (u : unitary A) : τ.GNS →ₗᵢ[ℂ] τ.GNS where
  toLinearMap := ((τ.gnsStarAlgHom (u : A)).comp
    (rightMul τ hτ (star u : A))).toLinearMap
  norm_map' x := by
    change ‖τ.gnsStarAlgHom (u : A) (rightMul τ hτ (star u : A) x)‖ = ‖x‖
    rw [ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.map_mem _ u.property)]
    exact ContinuousLinearMap.norm_map_of_mem_unitary
      (rightMul_mem_unitary τ hτ (star u)) x

@[simp] lemma conjugation_coe (u : unitary A) (a : A) :
    conjugation τ hτ u (τ.toPreGNS a : τ.GNS) =
      (τ.toPreGNS ((u : A) * a * (star u : A)) : τ.GNS) := by
  change τ.gnsStarAlgHom (u : A) (rightMul τ hτ (star u : A)
    (τ.toPreGNS a : τ.GNS)) = _
  rw [rightMul_coe, PositiveLinearMap.ofPreGNS_toPreGNS, left_coe, mul_assoc]

@[simp] lemma conjugation_vacuum (u : unitary A) :
    conjugation τ hτ u (vacuum τ) = vacuum τ := by
  rw [vacuum, conjugation_coe, mul_one, Unitary.mul_star_self_of_mem u.property]

lemma inner_vacuum_algebraVector (a : A) :
    inner ℂ (vacuum τ) (algebraVector τ a) = τ a := by
  change inner ℂ (algebraVector τ 1) (algebraVector τ a) = _
  rw [inner_algebraVector, star_one, one_mul]

lemma algebraVector_dense : DenseRange (algebraVector τ) := by
  have h := dense_cyclic_orbit τ
  change DenseRange (fun a => (τ.toPreGNS a : τ.GNS))
  simpa only [left_vacuum] using h

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialCommutation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped ComplexOrder InnerProductSpace

open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

@[simp] lemma starMap_vacuum : starMap τ hτ (vacuum τ) = vacuum τ := by
  change starMap τ hτ (algebraVector τ 1) = _
  rw [starMap_algebra, star_one]
  rfl

lemma rightMul_mem_commutant (a : A) :
    rightMul τ hτ a∈Set.centralizer (Set.range τ.gnsStarAlgHom) := by
  rintro _ ⟨b,rfl⟩
  exact left_right_commute τ hτ b a

end Kadison.TracialGNS

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialRightClosure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped ComplexOrder InnerProductSpace

open Complex ContinuousLinearMap UniformSpace Completion

noncomputable section

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

include hτ in
lemma bicommutant_vacuum_separating {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)))
    (hz : T (vacuum τ)=0) : T=0 := by
  apply ContinuousLinearMap.ext
  have he : ∀ a : A, T (algebraVector τ a)=0 := by
    intro a
    have hh := congrArg (fun V : τ.GNS →L[ℂ] τ.GNS => V (vacuum τ))
      (hT _ (rightMul_mem_commutant τ hτ a))
    simpa only [mul_apply_eq_comp,right_vacuum,algebraVector_apply,hz,map_zero] using hh.symm
  exact fun x => congrFun ((algebraVector_dense τ).equalizer T.continuous continuous_const (funext he)) x

end Kadison.TracialGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder

open Filter ContinuousLinearMapWOT

namespace Kadison.NormalGNS

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

include hτ

lemma eq_of_vacuum {S T : τ.GNS →L[ℂ] τ.GNS}
    (hS : S∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)))
    (hT : T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)))
    (he : S (vacuum τ)=T (vacuum τ)) : S=T := by
  apply sub_eq_zero.mp
  apply bicommutant_vacuum_separating τ hτ
  · intro a ha
    simp only [mul_sub,sub_mul,hS a ha,hT a ha]
  · exact sub_eq_zero.mpr he

end Kadison.NormalGNS

end

end
end

end OAI
end


