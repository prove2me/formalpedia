-- Prove2me | Definitions.Def_OAIQ039C024
-- name    : OAIQ039C024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:16:25.301009+00:00
-- url     : https://prove2.me/theorems/4fca0bb2-cff7-48d7-b983-2392342d2cfe
-- title:
--   Definitions bundle OAIQ039C024 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 3 definitions and 20 theorems. The definitions and types are `OAI.Kadison.FaithfulNormalFunctional.restricted`, `OAI.Kadison.FaithfulNormalFunctional.vector`, `OAI.Kadison.Polar.rightSupport`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_DiffuseProjection`, `Commutator_FactorComparison`, `Commutator_FaithfulNormalStateProducer`, `Commutator_FaithfulVectorGNS`, `Commutator_FiniteTestPatching`, `Commutator_GNSVectorEmbedding`, `Commutator_PartialIsometryOrder`, `Commutator_PartialUnitaryAlgebra`, `Commutator_PolarDecomposition`, `Commutator_PolarSupport`, `Commutator_ProjectionChains`.
--
--   **Imports.** It imports the bundles `OAIQ039C001`, `OAIQ039C002`, `OAIQ039C003`, `OAIQ039C006`, `OAIQ039C008` and `OAIQ039C009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C033`, `OAIQ039C034`, `OAIQ039C035`, `OAIQ039C036`, `OAIQ039C038`, `OAIQ039C039`, `OAIQ039C040` and `OAIQ039C041`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C001
import Definitions.Def_OAIQ039C002
import Definitions.Def_OAIQ039C003
import Definitions.Def_OAIQ039C006
import Definitions.Def_OAIQ039C008
import Definitions.Def_OAIQ039C009

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionChains
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter ContinuousLinearMapWOT

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.ProjectionChains

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem monotone_ultralimit [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (ω : Ultrafilter ι) (hω : (ω : Filter ι)≤atTop)
    (P : ι → H →L[ℂ] H) (hp : ∀ i, IsStarProjection (P i)) (hmono : Monotone P) :
    ∃ W : H →L[ℂ] H, IsStarProjection W ∧ (∀ i, P i≤W) ∧
      Tendsto (fun i => ofCLM (P i)) (ω : Filter ι) (𝓝 (ofCLM W)) ∧
      ∀ Q : H →L[ℂ] H, IsStarProjection Q → (∀ i, P i≤Q) → W≤Q := by
  obtain ⟨W,_,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω P 1 zero_le_one
    (fun i => (hp i).norm_le (P i))
  have hWot : Tendsto (fun i => ofCLM (P i)) (ω : Filter ι) (𝓝 (ofCLM W)) := by
    apply tendsto_iff_forall_inner_apply_tendsto.mpr
    intro x y
    simpa only [RCLike.star_def,inner_conj_symm,ofCLM_apply] using (hlim x y).star
  have hself : IsSelfAdjoint W := by
    have heq : star (ofCLM W)=ofCLM W := tendsto_nhds_unique hWot.star
      (hWot.congr' (Filter.Eventually.of_forall fun i => by
        change ofCLM (P i)=star (ofCLM (P i))
        apply toCLM_injective
        exact (hp i).isSelfAdjoint.star_eq.symm))
    exact congrArg toCLM heq
  have hWP : ∀ i, W*P i=P i := by
    intro i
    apply WeakOperatorLimit.right_eq hlim
    apply ((eventually_ge_atTop i).filter_mono hω).mono
    intro j hij
    exact ((hp i).le_iff_mul_eq_right (hp j)).mp (hmono hij)
  have hWsq : W*W=W := by
    have hh := WeakOperatorLimit.intertwine hlim 1 W (Filter.Eventually.of_forall
      fun i => by simpa only [mul_one] using (hWP i).symm)
    simpa only [mul_one] using hh.symm
  have hproj : IsStarProjection W := ⟨hWsq,hself⟩
  refine ⟨W,hproj,fun i => ((hp i).le_iff_mul_eq_right hproj).mpr (hWP i),hWot,?_⟩
  intro Q hQ hPQ
  have hh := WeakOperatorLimit.intertwine hlim Q 1 (Filter.Eventually.of_forall
    fun i => by simpa only [one_mul] using ((hp i).le_iff_mul_eq_left hQ).mp (hPQ i))
  apply (hproj.le_iff_mul_eq_left hQ).mpr
  simpa only [one_mul] using hh

variable (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)

variable (e : H →L[ℂ] H) (t : ℝ)

theorem cut_chain_upper (he : IsStarProjection e)
    (hτ : Continuous (fun T : H →WOT[ℂ] H => (τ T.toCLM).re))
    (c : Set (TraceCut M τ e t)) (hc : IsChain (·≤·) c) (hne : c.Nonempty) : BddAbove c := by
  let : Nonempty c := hne.to_subtype
  let : IsDirectedOrder c := hc.directedOn.isDirectedOrder
  let ω : Ultrafilter c := Ultrafilter.of atTop
  have hω : (ω : Filter c)≤atTop := Ultrafilter.of_le atTop
  let P : c → H →L[ℂ] H := fun v => v.val.val
  obtain ⟨W,hW,hPW,hlim,hLeast⟩ := monotone_ultralimit ω hω P (fun i => i.val.property.2.1)
    (fun _ _ h => h)
  have hscalar : ∀ x y, Tendsto (fun i => inner ℂ (P i x) y) (ω : Filter c)
      (𝓝 (inner ℂ (W x) y)) := by
    intro x y
    have h := tendsto_iff_forall_inner_apply_tendsto.mp hlim x y
    simpa only [RCLike.star_def,inner_conj_symm,ofCLM_apply] using h.star
  have hWM : W∈M := WeakOperatorLimit.mem_vonNeumann hscalar M
    (Filter.Eventually.of_forall fun i => i.val.property.1)
  have hWe : W≤e := hLeast e he (fun i => i.val.property.2.2.1)
  have htrace : (τ W).re≤t := le_of_tendsto ((hτ.tendsto (ofCLM W)).comp hlim)
    (Filter.Eventually.of_forall fun i : c => i.val.property.2.2.2)
  refine ⟨⟨W,hWM,hW,hWe,htrace⟩,?_⟩
  intro p hp
  exact hPW ⟨p,hp⟩

end Kadison.ProjectionChains

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DiffuseProjection
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.DiffuseProjection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)

variable (hM : HasNoMinimalProjections M)

include hM

theorem exists_prescribed_trace
    (hτ : Continuous (fun T : H →WOT[ℂ] H => (τ T.toCLM).re))
    {e : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e)
    {t : ℝ} (ht : 0≤t) (hte : t≤(τ e).re) :
    ∃ p∈M, IsStarProjection p ∧ p≤e ∧ (τ p).re=t := by
  let p0 : ProjectionChains.TraceCut M τ e t :=
    ⟨0,M.zero_mem,IsStarProjection.zero _,he.nonneg,by simpa using ht⟩
  let : Nonempty (ProjectionChains.TraceCut M τ e t) := ⟨p0⟩
  obtain ⟨p,hmax⟩ := zorn_le_nonempty
    (ProjectionChains.cut_chain_upper M τ e t he hτ)
  have hpM := p.property.1
  have hp := p.property.2.1
  have hpe := p.property.2.2.1
  have hpt := p.property.2.2.2
  refine ⟨p.val,hpM,hp,hpe,?_⟩
  apply le_antisymm hpt
  by_contra! hlt
  have hres : IsStarProjection (e-p.val) := hp.sub_of_mul_eq_left he
    ((hp.le_iff_mul_eq_left he).mp hpe)
  have hresM : e-p.val∈M := M.sub_mem heM hpM
  have hresn : e-p.val≠0 := by
    intro hz
    have hpE := sub_eq_zero.mp hz
    rw [hpE] at hte
    exact (not_lt_of_ge hte) hlt
  obtain ⟨q,hqM,hq,hqn,hqle,hqtrace⟩ := exists_small M τ hM hresM hres hresn
    (sub_pos.mpr hlt)
  have hpq : p.val*q=0 := by
    have hqfix := (hq.le_iff_mul_eq_right hres).mp hqle
    have hpefix := (hp.le_iff_mul_eq_left he).mp hpe
    calc
      _=p.val*((e-p.val)*q) := by rw [hqfix]
      _=0 := by rw [←mul_assoc,mul_sub,hpefix,hp.isIdempotentElem.eq,sub_self,zero_mul]
  have hsumproj : IsStarProjection (p.val+q) := hp.add hq hpq
  have hsume : p.val+q≤e := by
    calc
      _≤p.val+(e-p.val) := add_le_add_right hqle _
      _=e := by abel
  have hsumtrace : (τ (p.val+q)).re≤t := by
    rw [map_add,Complex.add_re]
    linarith
  let r : ProjectionChains.TraceCut M τ e t :=
    ⟨p.val+q,M.add_mem hpM hqM,hsumproj,hsume,hsumtrace⟩
  have hpr : p ≤ r := le_add_of_nonneg_right hq.nonneg
  have heq : r=p := le_antisymm (hmax hpr) hpr
  have hval := congrArg Subtype.val heq
  change p.val+q=p.val at hval
  exact hqn (add_left_cancel (hval.trans (add_zero p.val).symm))

end Kadison.DiffuseProjection

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PolarDecomposition
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

lemma initial_invariant (T B : H →L[ℂ] H) (hB : Commute (CFC.abs T) B) :
    ∀ x∈initial T, B x∈initial T := by
  intro x hx
  apply closure_minimal (t := {x : H | B x∈initial T}) ?_ ?_ hx
  · rintro y ⟨z,rfl⟩
    apply Submodule.le_topologicalClosure
    exact ⟨B z,congrArg (fun R : H →L[ℂ] H => R z) hB.eq⟩
  · exact (LinearMap.range (CFC.abs T).toLinearMap).isClosed_topologicalClosure.preimage B.continuous

lemma partialIsometry_commutes (T B : H →L[ℂ] H)
    (hB : Commute T B) (hsB : Commute T (star B)) :
    Commute (partialIsometry T) B := by
  have hab : Commute (CFC.abs T) B := hB.cfcAbs_left hsB
  have habs : Commute (CFC.abs T) (star B) := hsB.cfcAbs_left (by simpa using hB)
  have hp := projection_commutes (initial T) B (initial_invariant T B hab)
    (initial_invariant T (star B) habs)
  have hgen : ∀ x : initial T, partialIsometry T (B x)=B (partialIsometry T x) := by
    intro x
    refine (absToInitial_dense T).induction_on x
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    · intro y
      have haby := congrArg (fun R : H →L[ℂ] H => R y) hab.eq
      change CFC.abs T (B y)=B (CFC.abs T y) at haby
      have ht := congrArg (fun R : H →L[ℂ] H => R y) hB.eq
      change T (B y)=B (T y) at ht
      have hf : ∀ z, partialIsometry T (CFC.abs T z)=T z := fun z =>
        congrArg (fun R : H →L[ℂ] H => R z) (factorization T)
      change partialIsometry T (B (CFC.abs T y))=B (partialIsometry T (CFC.abs T y))
      rw [←haby,hf,hf]
      exact ht
  have hvp : ∀ x : H, partialIsometry T ((initial T).starProjection x)=partialIsometry T x :=
    fun x => congrArg (fun R : H →L[ℂ] H => R x) (partialIsometry_mul_initial T)
  change partialIsometry T*B=B*partialIsometry T
  ext x
  change partialIsometry T (B x)=B (partialIsometry T x)
  rw [←hvp (B x)]
  rw [show (initial T).starProjection (B x)=B ((initial T).starProjection x) from
    congrArg (fun R : H →L[ℂ] H => R x) hp]
  rw [hgen ⟨(initial T).starProjection x,(initial T).starProjection_apply_mem x⟩,hvp]

theorem partialIsometry_mem_vonNeumann (M : VonNeumannAlgebra H)
    {T : H →L[ℂ] H} (hT : T∈M) : partialIsometry T∈M := by
  change partialIsometry T∈M.carrier
  rw [←M.centralizer_centralizer']
  intro B hB
  have hb : Commute T B := hB T hT
  have hs : Commute T (star B) := by
    simpa only [star_star] using (show Commute (star T) B from hB (star T) (star_mem hT)).star_star
  exact (partialIsometry_commutes T B hb hs).eq.symm

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PolarSupport
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

def rightSupport (T : H →L[ℂ] H) : H →L[ℂ] H := (initial T).starProjection

lemma isProjection_rightSupport (T : H →L[ℂ] H) : IsStarProjection (rightSupport T) :=
  isStarProjection_starProjection

lemma mul_partialIsometry_of_mul (T e : H →L[ℂ] H) (he : e*T=T) :
    e*partialIsometry T=partialIsometry T := by
  have h : ∀ x : initial T, e (initialMap T x)=initialMap T x := by
    intro x
    refine (absToInitial_dense T).induction_on x
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro y
    rw [initialMap_abs]
    exact congrArg (fun R : H →L[ℂ] H => R y) he
  ext x
  exact h ((initial T).orthogonalProjectionOnto x)

lemma abs_mul_of_mul (T e : H →L[ℂ] H) (hT : T*e=T) : CFC.abs T*e=CFC.abs T := by
  ext x
  have ht : T (e x-x)=0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg (fun R : H →L[ℂ] H => R x) hT)
  have ha : CFC.abs T (e x-x)=0 := by
    apply norm_eq_zero.mp
    rw [norm_abs_apply,ht,norm_zero]
  change CFC.abs T (e x)=CFC.abs T x
  exact sub_eq_zero.mp (by simpa only [map_sub] using ha)

lemma rightSupport_le (T e : H →L[ℂ] H) (he : IsStarProjection e) (hT : T*e=T) :
    rightSupport T≤e := by
  have hs : star (CFC.abs T)=CFC.abs T := (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg T)).star_eq
  have hea : e*CFC.abs T=CFC.abs T := by
    simpa only [star_mul,hs,he.isSelfAdjoint.star_eq] using congrArg star (abs_mul_of_mul T e hT)
  have hfix : ∀ x : initial T, e x=x := by
    intro x
    refine (absToInitial_dense T).induction_on x
      (isClosed_eq (e.continuous.comp continuous_subtype_val) continuous_subtype_val) ?_
    intro y
    exact congrArg (fun R : H →L[ℂ] H => R y) hea
  apply ((isProjection_rightSupport T).le_iff_mul_eq_right he).mpr
  ext x
  exact hfix ⟨(initial T).starProjection x,(initial T).starProjection_apply_mem x⟩

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialIsometryOrder
attribute [-instance] _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Link

variable {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}

lemma target_mul (v : Link M e f) (hf : IsStarProjection f) : f*v.val=v.val := by
  have h := (v.final_projection.le_iff_mul_eq_right hf).mp v.target_le
  calc
    _=f*(v.final*v.val) := by rw [v.final_mul]
    _=v.val := by rw [←mul_assoc,h,v.final_mul]

end Link

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FactorComparison
attribute [-instance] _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Link

variable {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}

lemma residual_source_projection (v : Link M e f) (he : IsStarProjection e) :
    IsStarProjection (e-v.initial) :=
  v.initial_projection.sub_of_mul_eq_left he
    ((v.initial_projection.le_iff_mul_eq_left he).mp v.source_le)

lemma residual_target_projection (v : Link M e f) (hf : IsStarProjection f) :
    IsStarProjection (f-v.final) :=
  v.final_projection.sub_of_mul_eq_left hf
    ((v.final_projection.le_iff_mul_eq_left hf).mp v.target_le)

lemma residual_mul_initial (v : Link M e f) (he : IsStarProjection e)
    (w : Link M (e-v.initial) (f-v.final)) : w.val*v.initial=0 := by
  have hep := (v.initial_projection.le_iff_mul_eq_right he).mp v.source_le
  calc
    _=(w.val*(e-v.initial))*v.initial := by
      rw [w.mul_source (v.residual_source_projection he)]
    _=0 := by rw [mul_assoc,sub_mul,hep,v.initial_projection.isIdempotentElem.eq,sub_self,mul_zero]

lemma final_mul_residual (v : Link M e f) (hf : IsStarProjection f)
    (w : Link M (e-v.initial) (f-v.final)) : v.final*w.val=0 := by
  have hqf := (v.final_projection.le_iff_mul_eq_left hf).mp v.target_le
  calc
    _=v.final*((f-v.final)*w.val) := by
      rw [w.target_mul (v.residual_target_projection hf)]
    _=0 := by rw [←mul_assoc,mul_sub,hqf,v.final_projection.isIdempotentElem.eq,sub_self,zero_mul]

end Link

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FaithfulNormalStateProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology ComplexOrder

namespace Kadison

namespace FaithfulNormalFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (x : ℕ → H) (M : VonNeumannAlgebra H)

def restricted : M →ₚ[ℂ] ℂ where
  toFun a := functional x (a : H →L[ℂ] H)
  map_add' _ _ := (functional x).map_add _ _
  map_smul' _ _ := (functional x).map_smul _ _
  monotone' := fun _ _ h => (functional x).monotone h

end FaithfulNormalFunctional

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GNSVectorEmbedding
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open UniformSpace ContinuousLinearMap

namespace Kadison.VectorGNS

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (τ : A →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hτ : ∀ a,τ a=inner ℂ ξ (φ a ξ))

@[simp] lemma embedding_coe (a : A) :
    embedding τ φ ξ hτ (TracialGNS.algebraVector τ a)=φ a ξ := by
  change ((preIsometry τ φ ξ hτ).toContinuousLinearMap.extend
    (Completion.toComplL : τ.PreGNS →L[ℂ] τ.GNS))
    ((Completion.toComplL : τ.PreGNS →L[ℂ] τ.GNS) (τ.toPreGNS a))=_
  rw [extend_eq _ Completion.denseRange_coe (Completion.isUniformInducing_coe _)]
  rfl

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FaithfulVectorGNS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology ENNReal

namespace Kadison.FaithfulNormalFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (x : ℕ → H)

def vector : InfiniteAmplification.Space ℕ H := ⟨weighted x,weighted_mem x⟩

lemma vector_inner (T : H →L[ℂ] H) :
    inner ℂ (vector x) ((InfiniteAmplification.diagonal (H:=H) (ι:=ℕ)) T (vector x))=functional x T := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change inner ℂ ((Real.sqrt (weight x n):ℂ) • x n)
    (T ((Real.sqrt (weight x n):ℂ) • x n))=term x n T
  rw [map_smul,inner_smul_left,inner_smul_right]
  simp only [Complex.conj_ofReal,term]
  rw [←mul_assoc,←Complex.ofReal_mul,←pow_two,Real.sq_sqrt (weight_pos x n).le]

end Kadison.FaithfulNormalFunctional

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTestPatching
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.FiniteTest

section Signs

variable {I : Type*} [DecidableEq I]

@[simp] lemma sign_not (b : Bool) : sign (!b) = -sign b := by cases b <;> simp [sign]

@[simp] lemma sign_sq (b : Bool) : sign b * sign b = 1 := by cases b <;> norm_num [sign]

end Signs

end Kadison.FiniteTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryAlgebra
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

variable (A : Type*) [CStarAlgebra A]

namespace PartialUnitary

variable {A}

@[simp] lemma power_nat_succ (v : PartialUnitary A) (n : ℕ) :
    v.power (n+1 : ℕ)=v.val^(n+1) := rfl

end PartialUnitary

end Kadison.FinitePatching

end

end
end

end OAI
end


