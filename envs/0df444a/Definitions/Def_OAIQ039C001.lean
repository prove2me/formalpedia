-- Prove2me | Definitions.Def_OAIQ039C001
-- name    : OAIQ039C001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:11:06.903228+00:00
-- url     : https://prove2.me/theorems/c1237e45-bdf8-41e9-9c7e-fef4094faee0
-- title:
--   Definitions bundle OAIQ039C001 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 44 declarations of OpenAI's Lean: 13 definitions, 1 inductive type or structure, 1 instance and 29 theorems. The definitions and types are `OAI.Kadison.CStarContractions`, `OAI.Kadison.CentralAverage.CentralProjection`, `OAI.Kadison.CentralAverage.projectionElement`, `OAI.Kadison.Kaplansky.clip`, `OAI.Kadison.Kaplansky.lift`, `OAI.Kadison.Kaplansky.rationalClip`, `OAI.Kadison.Kaplansky.rationalKernel`, `OAI.Kadison.Kaplansky.rationalLift`, `OAI.Kadison.PartialIsometryOrder.Link`, `OAI.Kadison.PartialIsometryOrder.Link.final`, `OAI.Kadison.PartialIsometryOrder.Link.initial`, `OAI.Kadison.PartialIsometryOrder.OrthogonalLinks`, `OAI.Kadison.PartialIsometryOrder.familySpace`, `OAI.Kadison.PartialIsometryOrder.finiteProjection`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_BicommutantRange`, `Commutator_CStarRangeLifts`, `Commutator_CentralPinching`, `Commutator_CountableStarHomTests`, `Commutator_KaplanskyRational`, `Commutator_OrthogonalLinkFamily`, `Commutator_OrthogonalLinkSums`, `Commutator_PartialIsometryOrder`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C020`, `OAIQ039C024`, `OAIQ039C025`, `OAIQ039C029` and `OAIQ039C031`; the statements `OAI.Kadison.CentralAverage.exists_finite_average`, `OAI_Kadison_Decomposable_uniform_commutator_in_central_spectral_model`, `OAI_Kadison_Decomposable_uniform_commutator_in_representation_model` and `OAI.Kadison.PartialIsometryOrder.maximal_family_spans_of_full_support`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_BicommutantRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexStarModule CStarAlgebra

open ComplexStarModule

namespace Kadison.BicommutantRange

variable {B : Type*} [CStarAlgebra B]

lemma eq_of_selfAdjoint_contractions (S : StarSubalgebra ℂ B)
    (h : ∀ T∈Set.centralizer (Set.centralizer (S : Set B)),
      IsSelfAdjoint T → ‖T‖≤1 → T∈S) :
    Set.centralizer (Set.centralizer (S : Set B))=(S : Set B) := by
  have hs : ∀ T∈Set.centralizer (Set.centralizer (S : Set B)), IsSelfAdjoint T → T∈S := by
    intro T hT hsT
    by_cases hz : T=0
    · rw [hz]; exact S.zero_mem
    have hn : ‖T‖≠0 := norm_ne_zero_iff.mpr hz
    have hm : (‖T‖⁻¹:ℝ) • T∈Set.centralizer (Set.centralizer (S : Set B)) := by
      intro b hb
      simp only [mul_smul_comm,smul_mul_assoc,hT b hb]
    have hs' : IsSelfAdjoint ((‖T‖⁻¹:ℝ) • T) := (IsSelfAdjoint.all _).smul hsT
    have hnorm : ‖(‖T‖⁻¹:ℝ) • T‖≤1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg T)),inv_mul_cancel₀ hn]
    have hd := S.smul_mem (h _ hm hs' hnorm) (‖T‖:ℂ)
    simpa only [Complex.coe_smul,smul_smul,mul_inv_cancel₀ hn,one_smul] using hd
  let D := StarSubalgebra.centralizer ℂ ((StarSubalgebra.centralizer ℂ (S : Set B)) : Set B)
  have he : (D : Set B)=Set.centralizer (Set.centralizer (S : Set B)) := by
    simp only [D,StarSubalgebra.coe_centralizer_centralizer,StarMemClass.star_coe_eq,Set.union_self]
  apply Set.Subset.antisymm
  · intro T hT
    have hTD : T∈D := by rw [←SetLike.mem_coe,he]; exact hT
    let r : ℝ := 2⁻¹
    have hr : (ℜ T : B)∈D := by
      have h := D.smul_mem (D.add_mem hTD (D.star_mem' hTD)) (r:ℂ)
      rw [Complex.coe_smul] at h
      exact h
    have hi : (ℑ T : B)∈D := by
      have h := D.smul_mem (D.smul_mem (D.sub_mem hTD (D.star_mem' hTD)) (r:ℂ)) (-Complex.I)
      rw [Complex.coe_smul] at h
      exact h
    have hr' := hs (ℜ T) (by rw [←he]; exact hr) (ℜ T).property
    have hi' := hs (ℑ T) (by rw [←he]; exact hi) (ℑ T).property
    change T∈S
    have ht : (ℜ T:B)+Complex.I • (ℑ T:B)∈S := S.add_mem hr' (S.smul_mem hi' Complex.I)
    rw [realPart_add_I_smul_imaginaryPart] at ht
    exact ht
  · exact Set.subset_centralizer_centralizer

lemma starHom_range {A : Type*} [CStarAlgebra A] (φ : A →⋆ₐ[ℂ] B)
    (h : ∀ T∈Set.centralizer (Set.centralizer (Set.range φ)),
      IsSelfAdjoint T → ‖T‖≤1 → T∈Set.range φ) :
    Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ :=
  eq_of_selfAdjoint_contractions φ.range h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma operatorHom_range {A : Type*} [CStarAlgebra A] (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (h : ∀ T∈Set.centralizer (Set.centralizer (Set.range φ)),
      IsSelfAdjoint T → ‖T‖≤1 → T∈Set.range φ) :
    Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ :=
  starHom_range φ h

end Kadison.BicommutantRange

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyRational
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

def rationalClip (t : ℝ) : ℝ := 2*t/(1+t^2)

def rationalKernel (t : ℝ) : ℝ := (1+t^2)⁻¹

lemma denom_pos (t : ℝ) : 0<1+t^2 := by positivity

lemma continuous_rationalClip : Continuous rationalClip := by
  unfold rationalClip
  exact (continuous_const.mul continuous_id).div
    (continuous_const.add (continuous_id.pow 2)) (fun t => ne_of_gt (denom_pos t))

lemma rationalClip_bound (t : ℝ) : ‖rationalClip t‖≤1 := by
  rw [rationalClip,Real.norm_eq_abs,abs_div,abs_of_pos (denom_pos t)]
  apply (div_le_one (denom_pos t)).mpr
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith [sq_nonneg (|t|-1),sq_abs t]

def rationalLift (t : ℝ) : ℝ := t/(1+Real.sqrt (1-t^2))

lemma lift_denom_pos (t : ℝ) : 0<1+Real.sqrt (1-t^2) := by positivity

lemma continuous_rationalLift : Continuous rationalLift := by
  unfold rationalLift
  exact continuous_id.div
    (continuous_const.add ((continuous_const.sub (continuous_id.pow 2)).sqrt))
    (fun t => ne_of_gt (lift_denom_pos t))

lemma rationalClip_lift {t : ℝ} (ht : |t|≤1) :
    rationalClip (rationalLift t)=t := by
  have ht2 : 0≤1-t^2 := by
    have := sq_abs t
    nlinarith [abs_nonneg t]
  have hs := Real.sq_sqrt ht2
  have hd := ne_of_gt (lift_denom_pos t)
  unfold rationalClip rationalLift
  apply (div_eq_iff (ne_of_gt (denom_pos _))).mpr
  field_simp
  have he : (1+Real.sqrt (1-t^2))^2+t^2=2*(1+Real.sqrt (1-t^2)) := by nlinarith
  rw [he]
  ring

variable {A : Type*} [CStarAlgebra A]

def clip (a : A) : A := cfc rationalClip a

lemma clip_norm_le (a : A) : ‖clip a‖≤1 :=
  norm_cfc_le (by norm_num) (fun t _ => rationalClip_bound t)

lemma clip_selfAdjoint (a : A) : IsSelfAdjoint (clip a) := cfc_predicate _ _

def lift (a : A) : A := cfc rationalLift a

lemma lift_selfAdjoint (a : A) : IsSelfAdjoint (lift a) := cfc_predicate _ _

lemma clip_lift {a : A} (ha : IsSelfAdjoint a) (hn : ‖a‖≤1) : clip (lift a)=a := by
  nontriviality A
  rw [clip,lift,←cfc_comp rationalClip rationalLift a ha
    continuous_rationalClip.continuousOn continuous_rationalLift.continuousOn]
  calc
    cfc (rationalClip ∘ rationalLift) a = cfc (fun t:ℝ=>t) a := by
      apply cfc_congr
      intro t ht
      exact rationalClip_lift ((spectrum.norm_le_norm_of_mem ht).trans hn)
    _=a := cfc_id' ℝ a ha

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CStarRangeLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexStarModule CStarAlgebra

namespace Kadison.CStarRangeLifts

open Kaplansky ComplexStarModule

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable (φ : A →⋆ₐ[ℂ] B)

theorem selfAdjoint_contraction {b : B} (hb : IsSelfAdjoint b) (hn : ‖b‖≤1)
    (hr : b∈Set.range φ) : ∃ a : A, IsSelfAdjoint a ∧ ‖a‖≤1 ∧ φ a=b := by
  obtain ⟨a,ha⟩ := hr
  let a₀ : A := ℜ a
  have ha₀ : IsSelfAdjoint a₀ := (ℜ a).property
  have he : φ a₀=b := by rw [show a₀=(ℜ a:A) from rfl,map_realPart,ha,hb.coe_realPart]
  refine ⟨clip (lift a₀),clip_selfAdjoint _,clip_norm_le _,?_⟩
  rw [clip,φ.map_cfc rationalClip (lift a₀) continuous_rationalClip.continuousOn
    (by fun_prop) (lift_selfAdjoint _) ((lift_selfAdjoint a₀).map φ),lift,
    φ.map_cfc rationalLift a₀ continuous_rationalLift.continuousOn (by fun_prop) ha₀ (ha₀.map φ),he]
  exact clip_lift hb hn

end Kadison.CStarRangeLifts

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CentralPinching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.CentralAverage

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def CentralProjection := {p : H →L[ℂ] H // p∈M ∧ IsStarProjection p ∧
  p∈Set.centralizer (M : Set (H →L[ℂ] H))}

def projectionElement (p : CentralProjection M) : M := ⟨p.val,p.property.1⟩

end Kadison.CentralAverage

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CountableStarHomTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology

namespace Kadison

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace.SeparableSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

abbrev CStarContractions (A : Type*) [CStarAlgebra A] := {a : A // ‖a‖≤1}

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialIsometryOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure Link (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H) where
  val : H →L[ℂ] H
  mem : val∈M
  triple : val*star val*val=val
  source_le : star val*val≤e
  target_le : val*star val≤f

namespace Link

variable {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}

@[ext] lemma ext {v w : Link M e f} (h : v.val=w.val) : v=w := by
  cases v; cases w; cases h; rfl

def initial (v : Link M e f) : H →L[ℂ] H := star v.val*v.val

def final (v : Link M e f) : H →L[ℂ] H := v.val*star v.val

lemma initial_projection (v : Link M e f) : IsStarProjection v.initial := by
  constructor
  · change (star v.val*v.val)*(star v.val*v.val)=star v.val*v.val
    calc
      _=star v.val*(v.val*star v.val*v.val) := by noncomm_ring
      _=star v.val*v.val := by rw [v.triple]
  · exact IsSelfAdjoint.star_mul_self v.val

lemma final_projection (v : Link M e f) : IsStarProjection v.final := by
  constructor
  · change (v.val*star v.val)*(v.val*star v.val)=v.val*star v.val
    calc
      _=(v.val*star v.val*v.val)*star v.val := by noncomm_ring
      _=v.val*star v.val := by rw [v.triple]
  · exact IsSelfAdjoint.mul_star_self v.val

lemma mul_initial (v : Link M e f) : v.val*v.initial=v.val := by
  rw [initial,←mul_assoc,v.triple]

lemma final_mul (v : Link M e f) : v.final*v.val=v.val := v.triple

lemma mul_source (v : Link M e f) (he : IsStarProjection e) : v.val*e=v.val := by
  have h := (v.initial_projection.le_iff_mul_eq_left he).mp v.source_le
  calc
    _=(v.val*v.initial)*e := by rw [v.mul_initial]
    _=v.val := by rw [mul_assoc,h,v.mul_initial]

end Link

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_OrthogonalLinkFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H)

def OrthogonalLinks (S : Set (Link M e f)) : Prop :=
  S.Pairwise (fun v w => star v.val*w.val=0)

def familySpace (S : Set (Link M e f)) : Submodule ℂ H :=
  (Submodule.span ℂ {x : H | ∃ v∈S,∃ ξ : H,v.val ξ=x}).topologicalClosure

instance instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace (S : Set (Link M e f)) : CompleteSpace (familySpace M e f S) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_OrthogonalLinkSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H)

variable (S : Set (Link M e f)) (hS : OrthogonalLinks M e f S)

def finiteProjection (s : Finset S) : H →L[ℂ] H := ∑ v∈s,v.val.final

include hS

lemma family_cross {v w : S} (hne : v≠w) : star v.val.val*w.val.val=0 :=
  hS v.property w.property (fun h => hne (Subtype.ext h))

lemma family_final_cross {v w : S} (hne : v≠w) : v.val.final*w.val.final=0 := by
  change (v.val.val*star v.val.val)*(w.val.val*star w.val.val)=0
  calc
    _=v.val.val*(star v.val.val*w.val.val)*star w.val.val := by noncomm_ring
    _=0 := by rw [family_cross M e f S hS hne,mul_zero,zero_mul]

lemma finiteProjection_projection (s : Finset S) : IsStarProjection (finiteProjection M e f S s) := by
  classical
  constructor
  · change (∑ v∈s,v.val.final)*(∑ v∈s,v.val.final)=∑ v∈s,v.val.final
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.mul_sum,Finset.sum_eq_single_of_mem v hv]
    · exact v.val.final_projection.isIdempotentElem.eq
    · intro w hw hne
      exact family_final_cross M e f S hS hne.symm
  · change star (∑ v∈s,v.val.final)=∑ v∈s,v.val.final
    rw [star_sum]
    exact Finset.sum_congr rfl (fun v hv => v.val.final_projection.isSelfAdjoint.star_eq)

lemma finiteProjection_norm_le (s : Finset S) : ‖finiteProjection M e f S s‖≤1 :=
  (finiteProjection_projection M e f S hS s).norm_le _

lemma finiteProjection_mul_val (s : Finset S) {v : S} (hv : v∈s) :
    finiteProjection M e f S s*v.val.val=v.val.val := by
  classical
  rw [finiteProjection,Finset.sum_mul,Finset.sum_eq_single_of_mem v hv]
  · exact v.val.final_mul
  · intro w hw hne
    change (w.val.val*star w.val.val)*v.val.val=0
    rw [mul_assoc,family_cross M e f S hS hne,mul_zero]

omit hS in
lemma finiteProjection_target (s : Finset S) (hf : IsStarProjection f) :
    finiteProjection M e f S s*f=finiteProjection M e f S s := by
  rw [finiteProjection,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  exact (v.val.final_projection.le_iff_mul_eq_left hf).mp v.val.target_le

lemma finiteProjection_tendsto_generator (v : S) (x : H) :
    Tendsto (fun s : Finset S => finiteProjection M e f S s (v.val.val x)) atTop
      (𝓝 (v.val.val x)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop ({v}:Finset S)] with s hs
  exact (congrArg (fun T : H →L[ℂ] H => T x)
    (finiteProjection_mul_val M e f S hS s (hs (by simp)))).symm

lemma finiteProjection_tendsto_space {x : H} (hx : x∈familySpace M e f S) :
    Tendsto (fun s : Finset S => finiteProjection M e f S s x) atTop (𝓝 x) := by
  have hspan : ∀ y∈Submodule.span ℂ {x : H | ∃ v∈S,∃ ξ : H,v.val ξ=x},
      Tendsto (fun s : Finset S => finiteProjection M e f S s y) atTop (𝓝 y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v,hv,ξ,rfl⟩ := hy
      exact finiteProjection_tendsto_generator M e f S hS ⟨v,hv⟩ ξ
    | zero => simpa only [map_zero] using (tendsto_const_nhds (x:=(0:H)) (f:=atTop (α:=Finset S)))
    | add x y hx hy hxlim hylim =>
      simpa only [map_add] using hxlim.add hylim
    | smul c x hx hxlim =>
      simpa only [map_smul] using hxlim.const_smul c
  have hequi : Equicontinuous (fun s : Finset S => fun x : H => finiteProjection M e f S s x) :=
    (LipschitzWith.uniformEquicontinuous _ 1 (fun s =>
      ContinuousLinearMap.lipschitzWith_of_opNorm_le (finiteProjection_norm_le M e f S hS s))).equicontinuous
  exact (hequi x).tendsto_of_mem_closure
    (continuous_id.continuousAt.mono_left inf_le_left) hspan hx

theorem finiteProjection_tendsto (hf : IsStarProjection f)
    (hspan : (familySpace M e f S).starProjection=f) (x : H) :
    Tendsto (fun s : Finset S => finiteProjection M e f S s x) atTop (𝓝 (f x)) := by
  have hx : f x∈familySpace M e f S := by
    simpa only [hspan] using (familySpace M e f S).starProjection_apply_mem x
  have ht := finiteProjection_tendsto_space M e f S hS hx
  have he (s : Finset S) : finiteProjection M e f S s (f x)=finiteProjection M e f S s x :=
    congrArg (fun T : H →L[ℂ] H => T x) (finiteProjection_target M e f S s hf)
  simpa only [he] using ht

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end


