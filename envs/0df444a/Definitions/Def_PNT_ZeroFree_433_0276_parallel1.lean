-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0276_parallel1
-- name    : PNT_ZeroFree_433_0276_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:59:27.254304+00:00
-- url     : https://prove2.me/theorems/1b0f44e6-1ed7-42aa-9b73-fb5109c7fd3f
-- title:
--   Zero-free region foundations: RowCompletion.PeriodicRows [0276_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.RowCompletion.PeriodicRows
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/RowCompletion/PeriodicRows.lean#L252-L459

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0049
import Definitions.Def_PNT_ZeroFree_433_0061
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0105
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0224_parallel1_1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/RowCompletion/PeriodicRows.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical


namespace CompletedGauss


section

def reflectionSixActive (e:Fin 6) : Prop := 3≤e.val

def reflectionSixLabel (e:Fin 6) : Fin 3 := ⟨e.val%3,Nat.mod_lt _ (by decide)⟩

def reflectionSixValid {ι:Type*} (e:ι→Fin 6) : Prop :=
  ∀i,e i=0 ∨ reflectionSixActive (e i)

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def encodeReflectionSix (x:ΣA:Finset ι,A→Fin 3) : ι→Fin 6 := fun i=>
  if h:i∈x.1 then ⟨3+(x.2 ⟨i,h⟩).val,by have ht:=(x.2 ⟨i,h⟩).isLt; omega⟩ else 0

def reflectionSixSupport (e:ι→Fin 6) : Finset ι :=
  Finset.univ.filter (fun i=>reflectionSixActive (e i))

def decodeReflectionSix (e:ι→Fin 6) : ΣA:Finset ι,A→Fin 3 :=
  ⟨reflectionSixSupport e,fun i=>reflectionSixLabel (e i.val)⟩

omit [Fintype ι] in
lemma reflectionSixActive_encode (x:ΣA:Finset ι,A→Fin 3) (i:ι) :
    reflectionSixActive (encodeReflectionSix x i) ↔ i∈x.1 := by
  by_cases hi:i∈x.1
  · simp [encodeReflectionSix,hi,reflectionSixActive]
  · simp [encodeReflectionSix,hi,reflectionSixActive]

omit [Fintype ι] in
lemma encodeReflectionSix_valid (x:ΣA:Finset ι,A→Fin 3) :
    reflectionSixValid (encodeReflectionSix x) := by
  intro i
  by_cases hi:i∈x.1
  · exact Or.inr ((reflectionSixActive_encode x i).mpr hi)
  · left
    simp [encodeReflectionSix,hi]

lemma reflectionSixSupport_encode (x:ΣA:Finset ι,A→Fin 3) :
    reflectionSixSupport (encodeReflectionSix x)=x.1 := by
  ext i
  simp only [reflectionSixSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    reflectionSixActive_encode]

lemma encodeReflectionSix_injective :
    Function.Injective (encodeReflectionSix (ι:=ι)) := by
  intro x y hxy
  have hsets:x.1=y.1:=by
    rw [←reflectionSixSupport_encode x,←reflectionSixSupport_encode y,hxy]
  rcases x with ⟨A,e⟩
  rcases y with ⟨B,f⟩
  dsimp only at hsets
  subst B
  congr 1
  funext i
  have he:=congrFun hxy i.val
  simp only [encodeReflectionSix,dif_pos i.property] at he
  apply Fin.ext
  have hv:=congrArg Fin.val he
  exact Nat.add_left_cancel hv

lemma encode_decodeReflectionSix (e:ι→Fin 6) (he:reflectionSixValid e) :
    encodeReflectionSix (decodeReflectionSix e)=e := by
  funext i
  by_cases hi:reflectionSixActive (e i)
  · have him:i∈reflectionSixSupport e:=by simp [reflectionSixSupport,hi]
    dsimp only [encodeReflectionSix, decodeReflectionSix]
    rw [dif_pos him]
    apply Fin.ext
    change 3 + (e i).val % 3 = (e i).val
    have hl:=(e i).isLt
    dsimp only [reflectionSixActive] at hi
    omega
  · have him:i∉reflectionSixSupport e:=by simp [reflectionSixSupport,hi]
    have hz:e i=0:=(he i).resolve_right hi
    simp [encodeReflectionSix,decodeReflectionSix,him,hz]

lemma decode_encodeReflectionSix (x:ΣA:Finset ι,A→Fin 3) :
    decodeReflectionSix (encodeReflectionSix x)=x :=
  encodeReflectionSix_injective (encode_decodeReflectionSix _ (encodeReflectionSix_valid x))

def reflectionSixEquiv : (ΣA:Finset ι,A→Fin 3) ≃ {e:ι→Fin 6 // reflectionSixValid e} where
  toFun x:=⟨encodeReflectionSix x,encodeReflectionSix_valid x⟩
  invFun e:=decodeReflectionSix e.val
  left_inv:=decode_encodeReflectionSix
  right_inv e:=Subtype.ext (encode_decodeReflectionSix e.val e.property)

theorem sum_active_exceptional_eq_six {V:Type*} [AddCommMonoid V]
    (F:∀A:Finset ι,(A→Fin 3)→V) :
    (∑A:Finset ι,∑e:A→Fin 3,F A e)=
      ∑e:ι→Fin 6,if reflectionSixValid e then
        F (decodeReflectionSix e).1 (decodeReflectionSix e).2 else 0 := by
  have he:=Equiv.sum_comp (reflectionSixEquiv (ι:=ι))
    (fun e:{e:ι→Fin 6 // reflectionSixValid e}=>
      F (decodeReflectionSix e.val).1 (decodeReflectionSix e.val).2)
  have hs:(∑x:ΣA:Finset ι,A→Fin 3,F x.1 x.2)=
      ∑e:{e:ι→Fin 6 // reflectionSixValid e},F (decodeReflectionSix e.val).1 (decodeReflectionSix e.val).2 := by
    calc
      _=∑x:ΣA:Finset ι,A→Fin 3,
          F (decodeReflectionSix (encodeReflectionSix x)).1
            (decodeReflectionSix (encodeReflectionSix x)).2 := by
        apply Finset.sum_congr rfl
        intro x _
        exact (congrArg (fun y:ΣA:Finset ι,A→Fin 3=>F y.1 y.2)
          (decode_encodeReflectionSix x)).symm
      _=_ := he
  rw [Fintype.sum_sigma] at hs
  rw [hs,←Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter reflectionSixValid)
    (by simp) (fun e:ι→Fin 6=>F (decodeReflectionSix e).1 (decodeReflectionSix e).2)).symm

end
section

open ActualEisensteinCubic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance reflectionWeightField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P
noncomputable local instance reflectionWeightFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def reflectionStratumWeight (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (A:Finset ι) : ℂ :=
  (∏i∈A,(((actualSextic (P i) (hg i))⁻¹)^2) (σ A i)*
    phase (actualSextic (P i) (hg i)) (ψ A i) (j i) (ε A i))*
  (∏i∈(Finset.univ:Finset ι)\A,zeroFourierCoefficient (actualSextic (P i) (hg i)) (j i))

lemma reflectionStratumWeight_norm_le_one (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (hc:∀i,ringChar (Eis⧸P i)≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ) (hψ:∀A i,(ψ A i).IsPrimitive)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (A:Finset ι) :
    ‖reflectionStratumWeight P hg j ψ σ ε A‖≤1 := by
  have hactive (i:ι) : ‖(((actualSextic (P i) (hg i))⁻¹)^2) (σ A i)*
      phase (actualSextic (P i) (hg i)) (ψ A i) (j i) (ε A i)‖=1 := by
    rw [norm_mul,FiniteRayExpansion.norm_char_unit]
    simpa only [one_mul,actualSextic] using canonical_phase_norm (P i) (hg i) (hc i)
      (ψ A i) (hψ A i) (j i) (hj i) (ε A i)
  have hinactive (i:ι) : ‖zeroFourierCoefficient (actualSextic (P i) (hg i)) (j i)‖≤1 := by
    by_cases hi:j i=0
    · rw [hi]
      exact zeroFourierCoefficient_zero_norm_le_one _
    · have he:=canonical_zeroFourierCoefficient (P i) (hg i) (hc i) (j i) (hj i)
      have hz:zeroFourierCoefficient (actualSextic (P i) (hg i)) (j i)=0 := by
        simpa only [actualSextic,if_neg hi] using he
      rw [hz]
      simp
  rw [reflectionStratumWeight,norm_mul,norm_prod,norm_prod]
  simp only [hactive,Finset.prod_const_one,one_mul]
  exact Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun i _=>hinactive i)

def reflectionSixWeight (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (e:ι→Fin 6) : ℂ :=
  if reflectionSixValid e then reflectionStratumWeight P hg j ψ σ ε (reflectionSixSupport e) else 0

lemma reflectionSixWeight_norm_le_one (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (hc:∀i,ringChar (Eis⧸P i)≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ) (hψ:∀A i,(ψ A i).IsPrimitive)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (e:ι→Fin 6) :
    ‖reflectionSixWeight P hg j ψ σ ε e‖≤1 := by
  unfold reflectionSixWeight
  split_ifs
  · exact reflectionStratumWeight_norm_le_one P hg hc j hj ψ hψ σ ε _
  · simp

theorem sum_reflectionStratumWeight_eq_six (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ)
    (G:∀A:Finset ι,(A→Fin 3)→ℂ) :
    (∑A:Finset ι,∑e:A→Fin 3,reflectionStratumWeight P hg j ψ σ ε A*G A e)=
      ∑e:ι→Fin 6,reflectionSixWeight P hg j ψ σ ε e*
        G (decodeReflectionSix e).1 (decodeReflectionSix e).2 := by
  rw [sum_active_exceptional_eq_six]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:reflectionSixValid e <;> simp [reflectionSixWeight,he,decodeReflectionSix]


theorem sum_reflectionSixWeight_unpad (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (G:(ι→Fin 6)→ℂ) :
    (∑e:ι→Fin 6,reflectionSixWeight P hg j ψ σ ε e*G e)=
      ∑A:Finset ι,∑e:A→Fin 3,reflectionStratumWeight P hg j ψ σ ε A*
        G (encodeReflectionSix ⟨A,e⟩) := by
  rw [sum_reflectionStratumWeight_eq_six]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:reflectionSixValid e
  · rw [encode_decodeReflectionSix e he]
  · simp only [reflectionSixWeight,if_neg he,zero_mul]

end


end CompletedGauss

end

end OAI

end


