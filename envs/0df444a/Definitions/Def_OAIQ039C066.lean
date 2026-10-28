-- Prove2me | Definitions.Def_OAIQ039C066
-- name    : OAIQ039C066
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:19:20.980431+00:00
-- url     : https://prove2.me/theorems/d7d9603a-6687-40da-9f4a-b5a83ecbda93
-- title:
--   Definitions bundle OAIQ039C066 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 3 definitions and 4 theorems. The definitions and types are `OAI.Kadison.FreeBlocks.normalizedColumn`, `OAI.Kadison.MatrixTower.stageAlgebra`, `OAI.Kadison.TracialGNS.sumLeft`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_FreeNormalizedColumns`, `Commutator_InvariantSum`, `Commutator_MatrixTowerClosure`, `Commutator_NormalTraceProjection`, `Commutator_ProjectionRounding`.
--
--   **Imports.** It imports the bundles `OAIQ039C058`, `OAIQ039C059`, `OAIQ039C060` and `OAIQ039C061` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ039C071`; the statements `OAI.Kadison.FreeBlocks.normalized_errors`, `OAI.Kadison.FreeBlocks.normalized_fejer_entry` and `OAI.Kadison.TracialGNS.actual_word_structure`; the proofs of `OAI.Kadison.CornerPhase.exists_relative_corner_phase`, `OAI.Kadison.CornerSymmetrization.bound_small_projection`, `OAI.Kadison.FreeBlocks.free_hankel_bound`, `OAI.Kadison.FreeBlocks.normal_free_corner_bound`, `OAI.Kadison.FreeBlocks.normalized_errors`, `OAI.Kadison.FreeBlocks.normalized_fejer_entry` and `OAI.Kadison.TracialGNS.actual_word_structure`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C058
import Definitions.Def_OAIQ039C059
import Definitions.Def_OAIQ039C060
import Definitions.Def_OAIQ039C061

section
-- module Solutions.OAIQ039_CM.Commutator_FreeNormalizedColumns
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace TensorProduct ComplexOrder

open UniformSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι} (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)
  (hS : S i=f.range) (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

variable (d : D) (s : letterSpace t S j) (hs : ‖s‖=1)
  (x : letterSpace t S i) (hx : ‖x‖=1)

variable (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) d‖)

def normalizedColumn (n : ℕ) : multiplicityLevel t S j 0 →ₗᵢ[ℂ] t.functional.GNS where
  toLinearMap := (((‖TracialGNS.algebraVector (factorTrace t f hf) d‖⁻¹:ℝ):ℂ) •
    (repeatedOutput t S f hf hS hfree hij d x n).comp
      (repeatInsertion t S s hs n).toContinuousLinearMap).toLinearMap
  norm_map' v := by
    change ‖((‖TracialGNS.algebraVector (factorTrace t f hf) d‖⁻¹:ℝ):ℂ) •
      repeatedOutput t S f hf hS hfree hij d x n (repeatInsertion t S s hs n v)‖=‖v‖
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,
      abs_of_nonneg (norm_nonneg _),norm_repeatedOutput,hx,one_pow,mul_one,
      (repeatInsertion t S s hs n).norm_map,←mul_assoc,
      inv_mul_cancel₀ (ne_of_gt hr),one_mul]

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InvariantSum
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
open scoped InnerProductSpace ENNReal
open scoped ComplexOrder InnerProductSpace TensorProduct
open UniformSpace ContinuousLinearMap

namespace Kadison.TracialGNS

open PreHilbert HilbertTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (h1 : τ 1=1)

variable (J : ℕ → Type*) [∀ k, NormedAddCommGroup (J k)]
  [∀ k, InnerProductSpace ℂ (J k)] [∀ k, CompleteSpace (J k)]

def sumLeft (a : A) (k : ℕ) : sumLevel τ J k →L[ℂ] sumLevel τ J k :=
  HilbertTensor.map (wordLeft τ a k) 1

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalTraceProjection
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (hnormal : BoundedWOTContinuous M τ)

variable (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include hfaith in
theorem gns_noMinimal (hM : DiffuseProjection.HasNoMinimalProjections M) :
    DiffuseProjection.HasNoMinimalProjections (algebra M τ hτ hnormal) := by
  let representation := τ.gnsStarAlgHom
  intro p hpM hp hpn
  obtain ⟨a,rfl⟩ := hpM
  have ha := (gns_projection_iff M τ hfaith a).mp hp
  have han : (a : H →L[ℂ] H)≠0 := by
    intro hz
    have haz : a=0 := Subtype.ext hz
    exact hpn (by rw [haz,map_zero])
  have hap : IsStarProjection (a : H →L[ℂ] H) := ha.map M.toStarSubalgebra.subtype
  obtain ⟨q,hqM,hq,hqn,hqa,hqle⟩ := hM a a.property hap han
  let b : M := ⟨q,hqM⟩
  have hb : IsStarProjection b := projection_subtype M hqM hq
  have hble : representation b ≤ representation a :=
    (gns_projection_le_iff M τ hfaith hb ha).mpr hqle
  refine ⟨representation b,⟨b,rfl⟩,hb.map representation,?_,?_,hble⟩
  · intro hz
    have hbz : b=0 := (gns_injective M τ hfaith)
      (hz.trans (map_zero representation).symm)
    exact hqn (congrArg Subtype.val hbz)
  · intro he
    exact hqa (congrArg Subtype.val ((gns_injective M τ hfaith) he))

include hτ hnormal hfaith in
theorem exists_prescribed_projection_trace
    (hM : DiffuseProjection.HasNoMinimalProjections M)
    (e : M) (he : IsStarProjection e) {t : ℝ} (ht : 0≤t) (hte : t≤(τ e).re) :
    ∃ p : M, IsStarProjection p ∧ p≤e ∧ (τ p).re=t := by
  have htG : t≤(trace M τ (τ.gnsStarAlgHom e)).re := by rwa [trace_gns]
  obtain ⟨p,⟨a,ha⟩,hp,hpe,hpt⟩ := DiffuseProjection.exists_prescribed_trace
    (algebra M τ hτ hnormal) (trace M τ)
    (gns_noMinimal M τ hτ hnormal hfaith hM)
    (Complex.continuous_re.comp (trace_continuous M τ))
    (show τ.gnsStarAlgHom e ∈ algebra M τ hτ hnormal from ⟨e,rfl⟩)
    (he.map τ.gnsStarAlgHom) ht htG
  subst p
  have hpa := (gns_projection_iff M τ hfaith a).mp hp
  refine ⟨a,hpa,(gns_projection_le_iff M τ hfaith hpa he).mp hpe,?_⟩
  change (trace M τ (τ.gnsStarAlgHom a)).re=t at hpt
  simpa only [trace_gns] using hpt

include hτ hnormal hfaith in
theorem exists_projection_partition (hM : DiffuseProjection.HasNoMinimalProjections M)
    (n : ℕ) (e : M) (he : IsStarProjection e) {t : ℝ} (ht : 0≤t)
    (htrace : (τ e).re=(n:ℝ)*t) :
    ∃ p : Fin n → M, (∀ i, IsStarProjection (p i) ∧ p i≤e ∧ (τ (p i)).re=t) ∧
      (∀ i j, i≠j → p i*p j=0) ∧ ∑ i,p i=e := by
  induction n generalizing e with
  | zero =>
    have hez : e=0 := projection_zero_of_trace_re_zero M τ hfaith e he (by simpa using htrace)
    subst e
    refine ⟨Fin.elim0,?_,?_,?_⟩
    · exact fun i => Fin.elim0 i
    · exact fun i => Fin.elim0 i
    · simp
  | succ n ih =>
    have hte : t≤(τ e).re := by rw [htrace,Nat.cast_succ]; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    obtain ⟨p,hp,hple,hpt⟩ := exists_prescribed_projection_trace M τ hτ hnormal hfaith hM e he ht hte
    have her : IsStarProjection (e-p) := (hp.le_iff_sub he).mp hple
    have htr : (τ (e-p)).re=(n:ℝ)*t := by
      rw [map_sub,Complex.sub_re,htrace,hpt,Nat.cast_succ]
      ring
    obtain ⟨q,hq,hqq,hqsum⟩ := ih (e-p) her htr
    have hpq : ∀ i, p*q i=0 := by
      intro i
      have hfix := ((hq i).1.le_iff_mul_eq_right her).mp (hq i).2.1
      calc
        _=p*((e-p)*q i) := by rw [hfix]
        _=0 := by rw [←mul_assoc,mul_sub,(hp.le_iff_mul_eq_left he).mp hple,hp.isIdempotentElem.eq,sub_self,zero_mul]
    have hqp : ∀ i, q i*p=0 := by
      intro i
      simpa only [star_mul,hp.isSelfAdjoint.star_eq,(hq i).1.isSelfAdjoint.star_eq,star_zero] using congrArg star (hpq i)
    refine ⟨Fin.cons p q,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hp,hple,hpt⟩
      · exact ⟨(hq j).1,(hq j).2.1.trans (sub_le_self e hp.nonneg),(hq j).2.2⟩
    · intro i j hij
      revert hij
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j _ => hpq j) j
        exact fun h => (h rfl).elim
      · refine Fin.cases (fun _ => hqp i) (fun j h => hqq i j (by simpa using h)) j
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ,hqsum]
      abel

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionRounding
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (hnormal : BoundedWOTContinuous M τ)

variable (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include hτ hnormal hfaith in
theorem exists_rational_subprojection (hM : DiffuseProjection.HasNoMinimalProjections M)
    (e : M) (he : IsStarProjection e) (b : ℕ) (hb : 0<b) :
    ∃ (n : ℕ) (p : M), IsStarProjection p ∧ p≤e ∧
      (τ p).re=(n:ℝ)/(b:ℝ) ∧ (τ (e-p)).re<1/(b:ℝ) := by
  let n := ⌊(b:ℝ)*(τ e).re⌋₊
  have hbR : (0:ℝ)<b := Nat.cast_pos.mpr hb
  have he0 : 0≤(τ e).re := (τ.map_nonneg he.nonneg).1
  have hn : (n:ℝ)≤(b:ℝ)*(τ e).re := Nat.floor_le (mul_nonneg hbR.le he0)
  have hnt : (n:ℝ)/(b:ℝ)≤(τ e).re := (div_le_iff₀ hbR).mpr (by simpa only [mul_comm] using hn)
  obtain ⟨p,hp,hpe,hpt⟩ := exists_prescribed_projection_trace M τ hτ hnormal hfaith
    hM e he (div_nonneg (Nat.cast_nonneg _) hbR.le) hnt
  refine ⟨n,p,hp,hpe,hpt,?_⟩
  rw [map_sub,Complex.sub_re,hpt]
  apply (lt_div_iff₀ hbR).mpr
  have hlt : (b:ℝ)*(τ e).re<(n:ℝ)+1 := Nat.lt_floor_add_one _
  have hcancel : (n:ℝ)/(b:ℝ)*(b:ℝ)=(n:ℝ) := div_mul_cancel₀ _ hbR.ne'
  nlinarith

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTowerClosure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

def stageAlgebra : StarSubalgebra ℂ (H →L[ℂ] H) := ⨆ n,(concreteStage M F n).range

end Kadison.MatrixTower

end

end
end

end OAI
end


