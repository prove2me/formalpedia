-- Prove2me | solution 1 for APSCounting893.Main.bounded_modular_dimension_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:55:32.03778+00:00
-- url     : https://prove2.me/submissions/58669c58-94e5-4709-863f-83cb445a5d6b

import Definitions.Def_APSCounting893_Main_CircuitInputs
import Definitions.Def_APSCounting893_Main_Geometry
import Definitions.Def_APSCounting893_Main_ModularJacobianData
import Definitions.Def_APSCounting893_Main_SampledResultant
import Mathlib
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Size
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.NumberTheory.Chebyshev
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic
import Theorems.Thm_APSCounting893_Main_jacobian_independence_criterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_exists_coordinate_transcendence_basis
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma rational_scalar_eq_head (cs : List ℚ) : CoefficientPresentation.rational.scalar cs=cs.headD 0 := by
  cases cs with
  | nil => rfl
  | cons q qs =>
    unfold CoefficientPresentation.scalar CoefficientPresentation.generator
    rw [Finset.sum_eq_single 0]
    · change (q.num : ℚ)/(q.den : ℚ)*1=q
      rw [mul_one,Rat.num_div_den]
    · intro i hi hi0
      simp only [zero_pow hi0,mul_zero]
    · intro h
      exact (h (Finset.mem_range.mpr (by simp))).elim

end APSCounting893.Main
end Component_0

section Component_1
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
local instance : CharZero CoefficientPresentation.rational.Field := inferInstanceAs (CharZero ℚ)

lemma integerPolynomialEmbedding_injective (n : ℕ) : Function.Injective (integerPolynomialEmbedding n) :=
  (IsFractionRing.injective (MvPolynomial (Fin n) CoefficientPresentation.rational.Field) _).comp
    (MvPolynomial.map_injective (Int.castRingHom CoefficientPresentation.rational.Field) Int.cast_injective)

lemma IntegerPolynomialPair.add_value {n : ℕ} (p q : IntegerPolynomialPair n)
    (hp : p.2≠0) (hq : q.2≠0) : (p.add q).value=p.value+q.value := by
  have hp' : integerPolynomialEmbedding n p.2≠0 := by exact (map_ne_zero_iff _ (integerPolynomialEmbedding_injective n)).mpr hp
  have hq' : integerPolynomialEmbedding n q.2≠0 := by exact (map_ne_zero_iff _ (integerPolynomialEmbedding_injective n)).mpr hq
  simp only [add,value,map_add,map_mul]
  field_simp
  <;> ring

lemma IntegerPolynomialPair.sub_value {n : ℕ} (p q : IntegerPolynomialPair n)
    (hp : p.2≠0) (hq : q.2≠0) : (p.sub q).value=p.value-q.value := by
  have hp' : integerPolynomialEmbedding n p.2≠0 := by exact (map_ne_zero_iff _ (integerPolynomialEmbedding_injective n)).mpr hp
  have hq' : integerPolynomialEmbedding n q.2≠0 := by exact (map_ne_zero_iff _ (integerPolynomialEmbedding_injective n)).mpr hq
  simp only [sub,value,map_sub,map_mul]
  field_simp
  <;> ring

lemma IntegerPolynomialPair.mul_value {n : ℕ} (p q : IntegerPolynomialPair n) :
    (p.mul q).value=p.value*q.value := by simp only [mul,value,map_mul,div_mul_div_comm]

lemma IntegerPolynomialPair.div_value {n : ℕ} (p q : IntegerPolynomialPair n) :
    (p.div q).value=p.value/q.value := by
  simp [div,value,map_mul,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

end APSCounting893.Main
end Component_1

section Component_2
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
local instance : CharZero CoefficientPresentation.rational.Field := inferInstanceAs (CharZero ℚ)

lemma integerPolynomialEmbedding_C (n : ℕ) (z : ℤ) :
    integerPolynomialEmbedding n (MvPolynomial.C z)=(z : CircuitFunctionField .rational n) := by
  simp [integerPolynomialEmbedding]

lemma integerVariablePair_value {n : ℕ} (i : Fin n) :
    IntegerPolynomialPair.value ((MvPolynomial.X i,1) : IntegerPolynomialPair n) =
      algebraMap (MvPolynomial (Fin n) CoefficientPresentation.rational.Field)
        (CircuitFunctionField .rational n) (MvPolynomial.X i) := by
  simp [IntegerPolynomialPair.value,integerPolynomialEmbedding]

lemma integerConstantPair_den_ne_zero {n : ℕ} (q : ℚ) :
    (MvPolynomial.C (q.den : ℤ) : MvPolynomial (Fin n) ℤ)≠0 := by
  have hn : (q.den : ℤ)≠0 := by exact_mod_cast q.den_pos.ne'
  simpa only [map_zero] using (MvPolynomial.C_injective (Fin n) ℤ).ne hn

lemma integerConstantPair_value {n : ℕ} (cs : List ℚ) :
    IntegerPolynomialPair.value ((MvPolynomial.C (cs.headD 0).num,MvPolynomial.C ((cs.headD 0).den : ℤ)) : IntegerPolynomialPair n) =
      algebraMap (MvPolynomial (Fin n) CoefficientPresentation.rational.Field)
        (CircuitFunctionField .rational n) (MvPolynomial.C (CoefficientPresentation.rational.scalar cs)) := by
  rw [rational_scalar_eq_head]
  simp only [IntegerPolynomialPair.value,integerPolynomialEmbedding_C,Int.cast_natCast]
  let f : CoefficientPresentation.rational.Field →+* CircuitFunctionField .rational n :=
    (algebraMap (MvPolynomial (Fin n) CoefficientPresentation.rational.Field)
      (CircuitFunctionField .rational n)).comp MvPolynomial.C
  have hf : f ((cs.headD 0).num : CoefficientPresentation.rational.Field) /
      f ((cs.headD 0).den : CoefficientPresentation.rational.Field) = f (cs.headD 0) := by
    rw [←map_div₀]
    apply congrArg f
    exact Rat.num_div_den _
  simpa only [map_intCast,map_natCast,f,RingHom.comp_apply] using hf

end APSCounting893.Main
end Component_2

section Component_3
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma IntegerPolynomialPair.value_ne_zero_iff {n : ℕ} (p : IntegerPolynomialPair n) (hp : p.2≠0) :
    p.value≠0 ↔ p.1≠0 := by
  constructor
  · intro h hz
    apply h
    simp [value,hz]
  · intro hn
    apply div_ne_zero
    · simpa only [map_zero] using (integerPolynomialEmbedding_injective n).ne hn
    · simpa only [map_zero] using (integerPolynomialEmbedding_injective n).ne hp

lemma integerGateValue_compatible {n : ℕ} (prior : List (IntegerPolynomialPair n))
    (hden : ∀ p ∈ prior,p.2≠0) (g : ArithmeticGate n)
    (v : CircuitFunctionField .rational n) (hv : gateValue .rational (prior.map IntegerPolynomialPair.value) g=some v) :
    ∃ p : IntegerPolynomialPair n,integerGateValue prior g=some p ∧ p.2≠0 ∧ p.value=v := by
  classical
  cases g with
  | «variable» i =>
    refine ⟨(MvPolynomial.X i,1),rfl,one_ne_zero,?_⟩
    simpa only [gateValue,Option.some.injEq,integerVariablePair_value] using hv
  | «constant» cs =>
    refine ⟨(MvPolynomial.C (cs.headD 0).num,MvPolynomial.C ((cs.headD 0).den : ℤ)),rfl,
      integerConstantPair_den_ne_zero _,?_⟩
    rw [integerConstantPair_value]
    exact Option.some.inj hv
  | add a b =>
    cases ha : prior[a]? <;> cases hb : prior[b]? <;>
      simp [gateValue,List.getElem?_map,ha,hb] at hv
    rename_i p q
    refine ⟨p.add q,by simp [integerGateValue,ha,hb],
      mul_ne_zero (hden p (List.mem_of_getElem? ha)) (hden q (List.mem_of_getElem? hb)),?_⟩
    exact (IntegerPolynomialPair.add_value p q (hden p (List.mem_of_getElem? ha))
      (hden q (List.mem_of_getElem? hb))).trans hv
  | sub a b =>
    cases ha : prior[a]? <;> cases hb : prior[b]? <;>
      simp [gateValue,List.getElem?_map,ha,hb] at hv
    rename_i p q
    refine ⟨p.sub q,by simp [integerGateValue,ha,hb],
      mul_ne_zero (hden p (List.mem_of_getElem? ha)) (hden q (List.mem_of_getElem? hb)),?_⟩
    exact (IntegerPolynomialPair.sub_value p q (hden p (List.mem_of_getElem? ha))
      (hden q (List.mem_of_getElem? hb))).trans hv
  | mul a b =>
    cases ha : prior[a]? <;> cases hb : prior[b]? <;>
      simp [gateValue,List.getElem?_map,ha,hb] at hv
    rename_i p q
    refine ⟨p.mul q,by simp [integerGateValue,ha,hb],
      mul_ne_zero (hden p (List.mem_of_getElem? ha)) (hden q (List.mem_of_getElem? hb)),?_⟩
    exact (IntegerPolynomialPair.mul_value p q).trans hv
  | div a b =>
    cases ha : prior[a]? <;> cases hb : prior[b]? <;>
      simp [gateValue,List.getElem?_map,ha,hb] at hv
    rename_i p q
    have hqv : q.value≠0 := hv.1
    have hqn : q.1≠0 := (q.value_ne_zero_iff (hden q (List.mem_of_getElem? hb))).mp hqv
    refine ⟨p.div q,by simp [integerGateValue,ha,hb],
      mul_ne_zero (hden p (List.mem_of_getElem? ha)) hqn,?_⟩
    have heq : p.value/q.value=v := hv.2
    exact (IntegerPolynomialPair.div_value p q).trans heq

end APSCounting893.Main
end Component_3

section Component_4
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma integerCircuitValues_of_success {n : ℕ} (C : ArithmeticCircuit n)
    (values : List (CircuitFunctionField .rational n)) (hv : circuitValues .rational C=some values) :
    ∃ ps : List (IntegerPolynomialPair n),integerCircuitValues C=some ps ∧
      (∀ p ∈ ps,p.2≠0) ∧ ps.map IntegerPolynomialPair.value=values := by
  let actualStep := fun (acc : Option (List (CircuitFunctionField .rational n))) (g : ArithmeticGate n) => do
    let prior ← acc
    let v ← gateValue .rational prior g
    return prior++[v]
  let intStep := fun (acc : Option (List (IntegerPolynomialPair n))) (g : ArithmeticGate n) => do
    let prior ← acc
    let p ← integerGateValue prior g
    return prior++[p]
  have hfold (gs : List (ArithmeticGate n)) (ps : List (IntegerPolynomialPair n))
      (hden : ∀ p ∈ ps,p.2≠0) (vs : List (CircuitFunctionField .rational n))
      (hvs : gs.foldl actualStep (some (ps.map IntegerPolynomialPair.value))=some vs) :
      ∃ qs : List (IntegerPolynomialPair n),gs.foldl intStep (some ps)=some qs ∧
        (∀ q ∈ qs,q.2≠0) ∧ qs.map IntegerPolynomialPair.value=vs := by
    induction gs generalizing ps vs with
    | nil => exact ⟨ps,rfl,hden,Option.some.inj hvs⟩
    | cons g gs ih =>
      rw [List.foldl_cons] at hvs ⊢
      change gs.foldl actualStep ((gateValue .rational (ps.map IntegerPolynomialPair.value) g).bind
        (fun v => some (ps.map IntegerPolynomialPair.value++[v])))=some vs at hvs
      cases hg : gateValue .rational (ps.map IntegerPolynomialPair.value) g with
      | none =>
        have hnone : ∀ gs : List (ArithmeticGate n),gs.foldl actualStep none=none := by
          intro gs
          induction gs with
          | nil => rfl
          | cons g gs ih => exact ih
        simp only [hg,Option.bind_none,hnone] at hvs
        cases hvs
      | some v =>
        obtain ⟨p,hp,hpd,hpv⟩:=integerGateValue_compatible ps hden g v hg
        have hnew : ∀ q ∈ ps++[p],q.2≠0 := by
          intro q hq
          rcases List.mem_append.mp hq with hq|hq
          · exact hden q hq
          · have he : q=p := by simpa using hq
            simpa only [he] using hpd
        have heq : (ps++[p]).map IntegerPolynomialPair.value=ps.map IntegerPolynomialPair.value++[v] := by
          simp only [List.map_append,List.map_cons,List.map_nil,hpv]
        have hvs' : gs.foldl actualStep (some ((ps++[p]).map IntegerPolynomialPair.value))=some vs := by
          rw [heq]
          simpa only [hg,Option.bind_some] using hvs
        obtain ⟨qs,hqs,hqd,hqv⟩:=ih (ps++[p]) hnew vs hvs'
        refine ⟨qs,?_,hqd,hqv⟩
        change gs.foldl intStep ((integerGateValue ps g).bind (fun p => some (ps++[p])))=some qs
        simpa only [hp,Option.bind_some] using hqs
  exact hfold C.gates [] (by simp) values hv

end APSCounting893.Main
end Component_4

section Component_5
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma circuitPolynomials_fraction_value {n : ℕ} (P : CoefficientPresentation) (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit P C) (values : List (CircuitFunctionField P n))
    (hv : circuitValues P C=some values) (j : Fin C.outputs.length) :
    algebraMap (MvPolynomial (Fin n) P.Field) (CircuitFunctionField P n) (circuitPolynomials P C j)=
      (values[C.outputs[j]]?).getD 0 := by
  classical
  obtain ⟨vs,hvs,hout⟩:=hvalid.2
  have heq : vs=values := Option.some.inj (hvs.symm.trans hv)
  subst vs
  obtain ⟨v,f,hget,hf⟩:=hout C.outputs[j] (List.getElem_mem _)
  let z:=((circuitValues P C).getD [])[C.outputs[j]]?.getD 0
  have hz : z=v := by
    dsimp only [z]
    rw [hv]
    change (values[C.outputs[j]]?).getD 0=v
    rw [hget]
    rfl
  have hex : ∃ f : MvPolynomial (Fin n) P.Field,algebraMap _ (CircuitFunctionField P n) f=z :=
    ⟨f,hf.trans hz.symm⟩
  have hh : algebraMap (MvPolynomial (Fin n) P.Field) (CircuitFunctionField P n) (circuitPolynomials P C j)=z := by
    unfold circuitPolynomials
    dsimp only
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  simpa only [z,hv,Option.getD_some] using hh

end APSCounting893.Main
end Component_5

section Component_6
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
namespace IntegerPolynomialPair
noncomputable def degree {n : ℕ} (p : IntegerPolynomialPair n) : ℕ := max p.1.totalDegree p.2.totalDegree

lemma degree_add {n : ℕ} (p q : IntegerPolynomialPair n) : (p.add q).degree ≤ p.degree+q.degree := by
  change max (p.1*q.2+q.1*p.2).totalDegree (p.2*q.2).totalDegree ≤ _
  apply max_le
  · apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (le_max_left _ _) (le_max_right _ _))
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      change _ ≤ max p.1.totalDegree p.2.totalDegree+max q.1.totalDegree q.2.totalDegree
      omega
  · exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (le_max_right _ _) (le_max_right _ _))

lemma degree_sub {n : ℕ} (p q : IntegerPolynomialPair n) : (p.sub q).degree ≤ p.degree+q.degree := by
  change max (p.1*q.2-q.1*p.2).totalDegree (p.2*q.2).totalDegree ≤ _
  apply max_le
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (le_max_left _ _) (le_max_right _ _))
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      change _ ≤ max p.1.totalDegree p.2.totalDegree+max q.1.totalDegree q.2.totalDegree
      omega
  · exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (le_max_right _ _) (le_max_right _ _))

lemma degree_mul {n : ℕ} (p q : IntegerPolynomialPair n) : (p.mul q).degree ≤ p.degree+q.degree := by
  exact max_le ((MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (le_max_left _ _) (le_max_left _ _)))
    ((MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (le_max_right _ _) (le_max_right _ _)))

lemma degree_div {n : ℕ} (p q : IntegerPolynomialPair n) : (p.div q).degree ≤ p.degree+q.degree := by
  exact max_le ((MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (le_max_left _ _) (le_max_right _ _)))
    ((MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (le_max_right _ _) (le_max_left _ _)))
end IntegerPolynomialPair

lemma integerGateValue_degree_bound {n : ℕ} (prior : List (IntegerPolynomialPair n))
    (M : ℕ) (hM : 1≤M) (hprior : ∀ p ∈ prior,p.degree≤M)
    (g : ArithmeticGate n) (p : IntegerPolynomialPair n) (hp : integerGateValue prior g=some p) : p.degree≤2*M := by
  cases g with
  | «variable» i =>
    simp only [integerGateValue,Option.some.injEq] at hp
    subst p
    simp [IntegerPolynomialPair.degree]
    omega
  | «constant» cs =>
    simp only [integerGateValue,Option.some.injEq] at hp
    subst p
    simp only [IntegerPolynomialPair.degree,MvPolynomial.totalDegree_C,max_self]
    exact Nat.zero_le _
  | add a b | sub a b | mul a b | div a b =>
    cases ha : prior[a]? <;> cases hb : prior[b]? <;> simp [integerGateValue,ha,hb] at hp
    subst p
    rename_i p q
    have hp':=hprior p (List.mem_of_getElem? ha)
    have hq':=hprior q (List.mem_of_getElem? hb)
    first
    | exact (IntegerPolynomialPair.degree_add p q).trans (by omega)
    | exact (IntegerPolynomialPair.degree_sub p q).trans (by omega)
    | exact (IntegerPolynomialPair.degree_mul p q).trans (by omega)
    | exact (IntegerPolynomialPair.degree_div p q).trans (by omega)

end APSCounting893.Main
end Component_6

section Component_7
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma integerCircuitValues_degree_bound {n : ℕ} (C : ArithmeticCircuit n)
    (ps : List (IntegerPolynomialPair n)) (hps : integerCircuitValues C=some ps) :
    ∀ p ∈ ps,p.degree≤2^C.gates.length := by
  let step := fun (acc : Option (List (IntegerPolynomialPair n))) (g : ArithmeticGate n) => do
    let prior ← acc
    let p ← integerGateValue prior g
    return prior++[p]
  have hnone (gs : List (ArithmeticGate n)) : gs.foldl step none=none := by
    induction gs with
    | nil => rfl
    | cons g gs ih => exact ih
  have hfold (gs : List (ArithmeticGate n)) (prior : List (IntegerPolynomialPair n)) (M : ℕ)
      (hM : 1≤M) (hprior : ∀ p ∈ prior,p.degree≤M) (out : List (IntegerPolynomialPair n))
      (hout : gs.foldl step (some prior)=some out) : ∀ p ∈ out,p.degree≤2^gs.length*M := by
    induction gs generalizing prior M out with
    | nil =>
      have he : prior=out := Option.some.inj hout
      subst out
      simpa using hprior
    | cons g gs ih =>
      rw [List.foldl_cons] at hout
      change gs.foldl step ((integerGateValue prior g).bind (fun p => some (prior++[p])))=some out at hout
      cases hg : integerGateValue prior g with
      | none => simp only [hg,Option.bind_none,hnone] at hout;cases hout
      | some q =>
        have hqd:=integerGateValue_degree_bound prior M hM hprior g q hg
        have hnew : ∀ p ∈ prior++[q],p.degree≤2*M := by
          intro p hp
          rcases List.mem_append.mp hp with hp|hp
          · exact (hprior p hp).trans (by omega)
          · have he : p=q := by simpa using hp
            simpa only [he] using hqd
        have hh : gs.foldl step (some (prior++[q]))=some out := by
          simpa only [hg,Option.bind_some] using hout
        intro p hp
        have hb:=ih (prior++[q]) (2*M) (by omega) hnew out hh p hp
        simpa [pow_succ,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hb
  simpa only [mul_one] using hfold C.gates [] 1 le_rfl (by simp) ps hps

end APSCounting893.Main
end Component_7

section Component_8
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma integerCircuitOutput_spec {n : ℕ} (C : ArithmeticCircuit n) (hvalid : ValidCircuit .rational C)
    (j : Fin C.outputs.length) :
    (integerCircuitOutput C j).2≠0 ∧
      (integerCircuitOutput C j).value=
        algebraMap (MvPolynomial (Fin n) CoefficientPresentation.rational.Field)
          (CircuitFunctionField .rational n) (circuitPolynomials .rational C j) := by
  obtain ⟨values,hv,hout⟩:=hvalid.2
  obtain ⟨ps,hps,hden,hmap⟩:=integerCircuitValues_of_success C values hv
  obtain ⟨v,f,hget,hf⟩:=hout C.outputs[j] (List.getElem_mem _)
  have hchosen:=circuitPolynomials_fraction_value .rational C hvalid values hv j
  rw [←hmap,List.getElem?_map] at hget hchosen
  cases hp : ps[C.outputs[j]]? with
  | none => simp only [hp,Option.map_none] at hget;cases hget
  | some p =>
    have hlookup : integerCircuitOutput C j=p := by simp only [integerCircuitOutput,hps,Option.getD_some,hp]
    rw [hlookup]
    refine ⟨hden p (List.mem_of_getElem? hp),?_⟩
    simpa only [hp,Option.map_some,Option.getD_some] using hchosen.symm

lemma integerCircuitOutput_degree_bound {n : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (j : Fin C.outputs.length) :
    (integerCircuitOutput C j).degree≤2^C.gates.length := by
  obtain ⟨values,hv,hout⟩:=hvalid.2
  obtain ⟨ps,hps,hden,hmap⟩:=integerCircuitValues_of_success C values hv
  obtain ⟨v,f,hget,hf⟩:=hout C.outputs[j] (List.getElem_mem _)
  rw [←hmap,List.getElem?_map] at hget
  cases hp : ps[C.outputs[j]]? with
  | none => simp only [hp,Option.map_none] at hget;cases hget
  | some p =>
    have hlookup : integerCircuitOutput C j=p := by simp only [integerCircuitOutput,hps,Option.getD_some,hp]
    rw [hlookup]
    exact integerCircuitValues_degree_bound C ps hps p (List.mem_of_getElem? hp)

end APSCounting893.Main
end Component_8

section Component_9
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
open MvPolynomial
namespace APSCounting893.Main

noncomputable def rationalDifferentialBasis (K : Type) [CommRing K] [IsDomain K] (n : ℕ) :
    Module.Basis (Fin n) (FractionRing (MvPolynomial (Fin n) K))
      (KaehlerDifferential K (FractionRing (MvPolynomial (Fin n) K))) := by
  let P := MvPolynomial (Fin n) K
  let E := FractionRing P
  letI : Algebra.FormallyEtale P E := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  exact ((KaehlerDifferential.mvPolynomialBasis K (Fin n)).baseChange E).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K P E)

lemma rationalDifferentialBasis_apply (K : Type) [CommRing K] [IsDomain K] (n : ℕ) (j : Fin n) :
    rationalDifferentialBasis K n j = KaehlerDifferential.D K (FractionRing (MvPolynomial (Fin n) K))
      (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (MvPolynomial.X j)) := by
  simp only [rationalDifferentialBasis,Module.Basis.map_apply,Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul,one_smul,KaehlerDifferential.map_D]

end APSCounting893.Main
end Component_9

section Component_10
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial
namespace APSCounting893.Main

lemma polynomial_derivation_formula {K M σ : Type} [CommRing K] [Fintype σ]
    [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
    [IsScalarTower K (MvPolynomial σ K) M]
    (δ : Derivation K (MvPolynomial σ K) M) (p : MvPolynomial σ K) :
    δ p = ∑ j, (MvPolynomial.pderiv j p) • δ (MvPolynomial.X j) := by
  classical
  let b := KaehlerDifferential.mvPolynomialBasis K σ
  have hh := congrArg δ.liftKaehlerDifferential (b.sum_repr (KaehlerDifferential.D K (MvPolynomial σ K) p))
  simpa only [b,KaehlerDifferential.mvPolynomialBasis_apply,KaehlerDifferential.mvPolynomialBasis_repr_apply,
    map_sum,map_smul,Derivation.liftKaehlerDifferential_comp_D] using hh.symm

end APSCounting893.Main
end Component_10

section Component_11
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma derivation_aeval_chain {K L M σ : Type} [CommRing K] [CommRing L] [Algebra K L]
    [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M] [Fintype σ]
    (δ : Derivation K L M) (v : σ → L) (p : MvPolynomial σ K) :
    δ (MvPolynomial.aeval v p) = ∑ i, (MvPolynomial.aeval v (MvPolynomial.pderiv i p)) • δ (v i) := by
  classical
  let P := MvPolynomial σ K
  letI : Algebra P L := (MvPolynomial.aeval v).toRingHom.toAlgebra
  letI : IsScalarTower K P L := IsScalarTower.of_algebraMap_eq (fun c => (MvPolynomial.aeval v).commutes c |>.symm)
  letI : Module P M := Module.compHom M (algebraMap P L)
  letI : IsScalarTower P L M := IsScalarTower.of_algebraMap_smul (fun a m => rfl)
  letI : IsScalarTower K P M := IsScalarTower.of_algebraMap_smul (fun k m => by
    change (algebraMap P L (algebraMap K P k)) • m = k • m
    rw [← IsScalarTower.algebraMap_apply K P L,algebraMap_smul])
  have hh := polynomial_derivation_formula (δ.compAlgebraMap P) p
  change δ (MvPolynomial.aeval v p) = ∑ i,
    MvPolynomial.aeval v (MvPolynomial.pderiv i p) • δ (MvPolynomial.aeval v (MvPolynomial.X i)) at hh
  simpa only [MvPolynomial.aeval_X] using hh

end APSCounting893.Main
end Component_11

section Component_12
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def rationalPartialDerivation (K : Type) [CommRing K] [IsDomain K] (n : ℕ) (j : Fin n) :
    Derivation K (FractionRing (MvPolynomial (Fin n) K)) (FractionRing (MvPolynomial (Fin n) K)) :=
  KaehlerDifferential.linearMapEquivDerivation K _ ((rationalDifferentialBasis K n).coord j)

lemma rationalPartialDerivation_X (K : Type) [CommRing K] [IsDomain K] (n : ℕ) (j k : Fin n) :
    rationalPartialDerivation K n j
      (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (MvPolynomial.X k)) = if k=j then 1 else 0 := by
  classical
  change (rationalDifferentialBasis K n).repr
    (KaehlerDifferential.D K _ (algebraMap _ _ (MvPolynomial.X k))) j = _
  rw [← rationalDifferentialBasis_apply]
  simp [Finsupp.single_apply]

lemma rationalPartialDerivation_polynomial (K : Type) [CommRing K] [IsDomain K] (n : ℕ) (j : Fin n)
    (p : MvPolynomial (Fin n) K) :
    rationalPartialDerivation K n j (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)) p) =
      algebraMap _ (FractionRing (MvPolynomial (Fin n) K)) (MvPolynomial.pderiv j p) := by
  classical
  let P := MvPolynomial (Fin n) K
  let E := FractionRing P
  let v : Fin n → E := fun i => algebraMap P E (MvPolynomial.X i)
  have heval : MvPolynomial.aeval (R := K) v = IsScalarTower.toAlgHom K P E := by
    ext i <;> simp only [MvPolynomial.aeval_C,MvPolynomial.aeval_X] <;> rfl
  have hh := derivation_aeval_chain (rationalPartialDerivation K n j) v p
  have hX (i : Fin n) : rationalPartialDerivation K n j (v i) = if i=j then 1 else 0 := rationalPartialDerivation_X K n j i
  rw [heval] at hh
  change rationalPartialDerivation K n j (algebraMap P E p) = ∑ i,
    algebraMap P E (MvPolynomial.pderiv i p) • rationalPartialDerivation K n j (v i) at hh
  simpa only [hX,smul_ite,smul_zero,smul_eq_mul,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh

end APSCounting893.Main
end Component_12

section Component_13
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma integerPolynomialEmbedding_derivative {n : ℕ} (j : Fin n) (p : MvPolynomial (Fin n) ℤ) :
    rationalPartialDerivation CoefficientPresentation.rational.Field n j (integerPolynomialEmbedding n p)=
      integerPolynomialEmbedding n (MvPolynomial.pderiv j p) := by
  simp only [integerPolynomialEmbedding,RingHom.comp_apply,rationalPartialDerivation_polynomial,
    MvPolynomial.pderiv_map]

lemma IntegerPolynomialPair.derivative_den_ne_zero {n : ℕ} (j : Fin n) (p : IntegerPolynomialPair n)
    (hp : p.2≠0) : (p.derivative j).2≠0 := pow_ne_zero 2 hp

lemma IntegerPolynomialPair.derivative_value {n : ℕ} (j : Fin n) (p : IntegerPolynomialPair n) :
    (p.derivative j).value=rationalPartialDerivation CoefficientPresentation.rational.Field n j p.value := by
  simp only [derivative,value,map_sub,map_mul,map_pow,Derivation.leibniz_div,
    integerPolynomialEmbedding_derivative,smul_eq_mul]
  simp [div_eq_mul_inv,inv_pow,mul_comm,mul_left_comm,mul_assoc]

end APSCounting893.Main
end Component_13

section Component_14
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma integerMatrixDenominator_ne_zero {n r : ℕ} (A : Matrix (Fin r) (Fin r) (IntegerPolynomialPair n))
    (hA : ∀ i j,(A i j).2≠0) : integerMatrixDenominator A≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact Finset.prod_ne_zero_iff.mpr (fun j hj => hA i j)

lemma clearedIntegerMatrix_value {n r : ℕ} (A : Matrix (Fin r) (Fin r) (IntegerPolynomialPair n))
    (hA : ∀ i j,(A i j).2≠0) (i j : Fin r) :
    integerPolynomialEmbedding n (clearedIntegerMatrix A i j)=
      integerPolynomialEmbedding n (∏ k,(A i k).2)*(A i j).value := by
  classical
  have hp : integerPolynomialEmbedding n (A i j).2≠0 := by
    simpa only [map_zero] using (integerPolynomialEmbedding_injective n).ne (hA i j)
  rw [←Finset.mul_prod_erase Finset.univ (fun k => (A i k).2) (Finset.mem_univ j)]
  simp only [clearedIntegerMatrix,map_mul,IntegerPolynomialPair.value]
  field_simp
  <;> ring

lemma integerMatrixDeterminantPair_value {n r : ℕ} (A : Matrix (Fin r) (Fin r) (IntegerPolynomialPair n))
    (hA : ∀ i j,(A i j).2≠0) :
    (integerMatrixDeterminantPair A).value=(Matrix.of fun i j => (A i j).value).det := by
  classical
  have hD:=integerMatrixDenominator_ne_zero A hA
  have hD' : integerPolynomialEmbedding n (integerMatrixDenominator A)≠0 := by
    simpa only [map_zero] using (integerPolynomialEmbedding_injective n).ne hD
  have hdet : integerPolynomialEmbedding n (clearedIntegerMatrix A).det=
      integerPolynomialEmbedding n (integerMatrixDenominator A)*(Matrix.of fun i j => (A i j).value).det := by
    rw [RingHom.map_det]
    change (Matrix.of fun i j => integerPolynomialEmbedding n (clearedIntegerMatrix A i j)).det=_
    simp_rw [clearedIntegerMatrix_value A hA]
    simpa only [integerMatrixDenominator,map_prod,Matrix.of_apply] using
      Matrix.det_mul_column (fun i => integerPolynomialEmbedding n (∏ k,(A i k).2))
        (Matrix.of fun i j => (A i j).value)
  change integerPolynomialEmbedding n (clearedIntegerMatrix A).det /
    integerPolynomialEmbedding n (integerMatrixDenominator A)=_
  rw [hdet]
  exact mul_div_cancel_left₀ _ hD'

end APSCounting893.Main
end Component_14

section Component_15
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma circuitJacobianIntegerPairs_den_ne_zero {n k : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) (i j : Fin k) :
    (circuitJacobianIntegerPairs C o v i j).2≠0 :=
  IntegerPolynomialPair.derivative_den_ne_zero _ _ (integerCircuitOutput_spec C hvalid (o i)).1

lemma circuitJacobianIntegerPairs_value {n k : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) (i j : Fin k) :
    (circuitJacobianIntegerPairs C o v i j).value=
      algebraMap (MvPolynomial (Fin n) CoefficientPresentation.rational.Field) (CircuitFunctionField .rational n)
        (MvPolynomial.pderiv (v j) (circuitPolynomials .rational C (o i))) := by
  rw [circuitJacobianIntegerPairs,IntegerPolynomialPair.derivative_value,
    (integerCircuitOutput_spec C hvalid (o i)).2,rationalPartialDerivation_polynomial]

lemma circuitJacobianIntegerMinor_ne_zero_iff {n k : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) :
    circuitJacobianIntegerMinor C o v≠0 ↔
      (Matrix.of fun i j => MvPolynomial.pderiv (v j) (circuitPolynomials .rational C (o i))).det≠0 := by
  let A:=circuitJacobianIntegerPairs C o v
  have hA : ∀ i j,(A i j).2≠0 := circuitJacobianIntegerPairs_den_ne_zero C hvalid o v
  have hval:=integerMatrixDeterminantPair_value A hA
  dsimp only [A] at hval
  simp_rw [circuitJacobianIntegerPairs_value C hvalid o v] at hval
  have hmap := RingHom.map_det
    (algebraMap (MvPolynomial (Fin n) CoefficientPresentation.rational.Field) (CircuitFunctionField .rational n))
    (Matrix.of fun i j => MvPolynomial.pderiv (v j) (circuitPolynomials .rational C (o i)))
  have heq : (integerMatrixDeterminantPair A).value=
      algebraMap (MvPolynomial (Fin n) CoefficientPresentation.rational.Field) (CircuitFunctionField .rational n)
        (Matrix.of fun i j => MvPolynomial.pderiv (v j) (circuitPolynomials .rational C (o i))).det := by
    exact hval.trans hmap.symm
  have hiff:=(integerMatrixDeterminantPair A).value_ne_zero_iff (integerMatrixDenominator_ne_zero A hA)
  rw [heq] at hiff
  exact hiff.symm.trans (by
    constructor
    · intro h hz;apply h;rw [hz,map_zero]
    · intro h;simpa only [map_zero] using (IsFractionRing.injective
        (MvPolynomial (Fin n) CoefficientPresentation.rational.Field) (CircuitFunctionField .rational n)).ne h)

end APSCounting893.Main
end Component_15

section Component_16
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace APSCounting893.Main

lemma circuitJacobianComplexMinor_map {n k : ℕ} (C : ArithmeticCircuit n)
    (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) :
    MvPolynomial.map (algebraMap ℚ ℂ)
      (Matrix.of fun i j => MvPolynomial.pderiv (v j) (circuitPolynomials .rational C (o i))).det=
        (Matrix.of fun i j => MvPolynomial.pderiv (v j) (rationalComplexPolynomials C (o i))).det := by
  have hh:=RingHom.map_det (MvPolynomial.map (algebraMap ℚ ℂ))
    (Matrix.of fun i j => (MvPolynomial.pderiv (v j) (circuitPolynomials .rational C (o i)) : MvPolynomial (Fin n) ℚ))
  apply hh.trans
  apply congrArg Matrix.det
  funext i j
  change MvPolynomial.map (algebraMap ℚ ℂ) (MvPolynomial.pderiv (v j) (circuitPolynomials .rational C (o i)))=_
  exact MvPolynomial.pderiv_map.symm

lemma circuitJacobianIntegerMinor_ne_zero_iff_complex {n k : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) :
    circuitJacobianIntegerMinor C o v≠0 ↔
      (Matrix.of fun i j => MvPolynomial.pderiv (v j) (rationalComplexPolynomials C (o i))).det≠0 := by
  rw [circuitJacobianIntegerMinor_ne_zero_iff C hvalid o v,←circuitJacobianComplexMinor_map]
  have hinj:=MvPolynomial.map_injective (σ:=Fin n) (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  constructor
  · intro h
    simpa only [map_zero] using hinj.ne h
  · intro h hz
    apply h
    rw [hz]
    exact map_zero _

end APSCounting893.Main
end Component_16

section Component_17

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma evaluation_substitution {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (p : Polynomials K m) (x : Affine K n) :
    eval x (eval₂Hom MvPolynomial.C F p) = eval (evaluate F x) p := by
  have heq : (eval x).comp (eval₂Hom MvPolynomial.C F) = eval (evaluate F x) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro i; simp [evaluate]
  exact RingHom.congr_fun heq p

lemma image_vanishingIdeal_eq_kernel {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) :
    vanishingIdeal K (Set.range (evaluate F)) = RingHom.ker (eval₂Hom MvPolynomial.C F) := by
  ext p
  constructor
  · intro hp
    rw [RingHom.mem_ker]
    apply MvPolynomial.funext
    intro x
    rw [evaluation_substitution]
    simpa only [map_zero, aeval_def, Algebra.algebraMap_self, eval₂_id] using
      hp (evaluate F x) (Set.mem_range_self x)
  · intro hp y hy
    obtain ⟨x, rfl⟩ := hy
    rw [RingHom.mem_ker] at hp
    rw [aeval_def, Algebra.algebraMap_self, eval₂_id, ← evaluation_substitution, hp, map_zero]

lemma hasAPS_iff_annihilator {n m : ℕ} (F : PolynomialMap ℂ n m) :
    hasAPS F ↔ ∀ p ∈ annihilator F, eval (0 : Affine ℂ m) p = 0 := by
  unfold hasAPS imageClosure RSCapacity.zClosure
  rw [image_vanishingIdeal_eq_kernel]
  rfl

lemma isAlgSet_zeroLocus {K : Type} [Field K] {n : ℕ}
    (I : Ideal (Polynomials K n)) : RSCapacity.IsAlgSet (zeroLocus K I) := by
  refine ⟨I, ?_⟩
  ext x
  simp only [mem_zeroLocus_iff, RSCapacity.zeroSet, Set.mem_setOf_eq,
    aeval_def, Algebra.algebraMap_self, eval₂_id, SetLike.mem_coe]

lemma isAlgSet_eq_zeroLocus {K : Type} [Field K] {n : ℕ}
    {X : Set (Affine K n)} (hX : RSCapacity.IsAlgSet X) :
    X = zeroLocus K (vanishingIdeal K X) := by
  apply Set.Subset.antisymm (zeroLocus_vanishingIdeal_le X)
  obtain ⟨S, rfl⟩ := hX
  intro x hx p hp
  have hv : p ∈ vanishingIdeal K (RSCapacity.zeroSet S) := by
    intro y hy
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hy p hp
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hx p hv

lemma irreducibleAffine_ideal_prime {K : Type} [Field K] {n : ℕ}
    {X : Set (Affine K n)} (hX : IrreducibleAffine X) :
    (vanishingIdeal K X).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro htop
    obtain ⟨x, hx⟩ := hX.1
    have hone : (1 : Polynomials K n) ∈ vanishingIdeal K X := by rw [htop]; trivial
    have := hone x hx
    simpa using this
  · intro p q hpq
    let A := RSCapacity.zeroSet ({p} : Set (Polynomials K n))
    let B := RSCapacity.zeroSet ({q} : Set (Polynomials K n))
    have hAB : X ⊆ A ∪ B := by
      intro x hx
      have hprod : eval x p * eval x q = 0 := by
        simpa only [map_mul, aeval_def, Algebra.algebraMap_self, eval₂_id] using hpq x hx
      rcases mul_eq_zero.mp hprod with hp | hq
      · left; simpa [A, RSCapacity.zeroSet] using hp
      · right; simpa [B, RSCapacity.zeroSet] using hq
    rcases hX.2.2 A B ⟨{p}, rfl⟩ ⟨{q}, rfl⟩ hAB with hA | hB
    · left
      intro x hx
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using (hA hx) p (Set.mem_singleton p)
    · right
      intro x hx
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using (hB hx) q (Set.mem_singleton q)

lemma prime_ideal_irreducibleAffine {K : Type} [Field K] {n : ℕ}
    {X : Set (Affine K n)} (hne : X.Nonempty) (hclosed : RSCapacity.IsAlgSet X)
    (hprime : (vanishingIdeal K X).IsPrime) : IrreducibleAffine X := by
  classical
  refine ⟨hne, hclosed, ?_⟩
  intro A B hA hB hAB
  by_cases hXA : X ⊆ A
  · exact Or.inl hXA
  by_cases hXB : X ⊆ B
  · exact Or.inr hXB
  obtain ⟨x, hx, hxA⟩ := Set.not_subset.mp hXA
  obtain ⟨y, hy, hyB⟩ := Set.not_subset.mp hXB
  rw [isAlgSet_eq_zeroLocus hA] at hxA
  rw [isAlgSet_eq_zeroLocus hB] at hyB
  simp only [mem_zeroLocus_iff, not_forall, exists_prop] at hxA hyB
  obtain ⟨p, hpA, hpx⟩ := hxA
  obtain ⟨q, hqB, hqy⟩ := hyB
  have hpq : p * q ∈ vanishingIdeal K X := by
    intro z hz
    rcases hAB hz with hzA | hzB
    · simp only [map_mul, hpA z hzA, zero_mul]
    · simp only [map_mul, hqB z hzB, mul_zero]
  rcases hprime.mem_or_mem hpq with hpX | hqX
  · exact (hpx (hpX x hx)).elim
  · exact (hqy (hqX y hy)).elim

lemma vanishingIdeal_zClosure {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) :
    vanishingIdeal K (RSCapacity.zClosure X) = vanishingIdeal K X := by
  apply le_antisymm
  · exact vanishingIdeal_anti_mono (zeroLocus_vanishingIdeal_le X)
  · intro p hp x hx
    exact hx p hp

lemma irreducibleAffine_imageClosure {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : IrreducibleAffine (imageClosure F) := by
  apply prime_ideal_irreducibleAffine
  · exact ⟨evaluate F 0, zeroLocus_vanishingIdeal_le _ (Set.mem_range_self 0)⟩
  · exact isAlgSet_zeroLocus _
  · unfold imageClosure
    rw [vanishingIdeal_zClosure, image_vanishingIdeal_eq_kernel]
    exact RingHom.ker_isPrime _

noncomputable def coordinatePullback {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) :
    Polynomials K m →+* CoordinateRing X :=
  (Ideal.Quotient.mk (vanishingIdeal K X)).comp (eval₂Hom MvPolynomial.C F)

noncomputable def coordinatePullbackAlgebra {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) :
    Algebra (Polynomials K m) (CoordinateRing X) := (coordinatePullback X F).toAlgebra


end APSCounting893.Main
end Component_17

section Component_18
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma exists_independent_image_coordinates {n m r : ℕ} (F : PolynomialMap ℂ n (m+1))
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞)) :
    ∃ g : Fin r → Fin (m+1), Function.Injective g ∧ AlgebraicIndependent ℂ (F ∘ g) := by
  classical
  let S := MvPolynomial (Fin (m+1)) ℂ
  let R := MvPolynomial (Fin n) ℂ
  let P : Ideal S := RingHom.ker (MvPolynomial.aeval F).toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime _
  obtain ⟨s,hind,hcard⟩ := OAI.PiExponent.FormalInterpolation.mvPolynomial_exists_coordinate_transcendence_basis P
  have hDim := OAI.PiExponent.FormalInterpolation.mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat P
  have hP : vanishingIdeal ℂ (imageClosure F) = P := by
    rw [imageClosure,vanishingIdeal_zClosure,image_vanishingIdeal_eq_kernel]
    rfl
  change ringKrullDim (S ⧸ vanishingIdeal ℂ (imageClosure F)) = ((r : ℕ∞) : WithBot ℕ∞) at hdim
  rw [hP] at hdim
  have htr : (Algebra.trdeg ℂ (FractionRing (S ⧸ P))).toNat = r := by
    exact_mod_cast hDim.symm.trans hdim
  have hsr : s.card = r := hcard.trans htr
  let f₀ : (S ⧸ P) →ₐ[ℂ] FractionRing (S ⧸ P) := IsScalarTower.toAlgHom ℂ (S ⧸ P) _
  have he (i : s) : f₀ (Ideal.Quotient.mk P (MvPolynomial.X i.1)) =
      algebraMap S (FractionRing (S ⧸ P)) (MvPolynomial.X i.1) := by
    dsimp only [f₀]
    rw [IsScalarTower.toAlgHom_apply,IsScalarTower.algebraMap_apply S (S ⧸ P) (FractionRing (S ⧸ P))]
    rfl
  have hquot : AlgebraicIndependent ℂ (fun i : s => Ideal.Quotient.mk P (MvPolynomial.X i.1)) := by
    apply AlgebraicIndependent.of_comp f₀
    have hef : (f₀ ∘ (fun i : s => Ideal.Quotient.mk P (MvPolynomial.X i.1))) =
        fun i : s => algebraMap S (FractionRing (S ⧸ P)) (MvPolynomial.X i.1) := funext he
    rw [hef]
    exact hind
  let f : (S ⧸ P) →ₐ[ℂ] R := Ideal.Quotient.liftₐ P (MvPolynomial.aeval F) (fun p hp => hp)
  have hfapp (p : S) : f (Ideal.Quotient.mk P p) = MvPolynomial.aeval F p := rfl
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f.toRingHom).mpr
    intro x hx
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change MvPolynomial.aeval F p = 0
    change f (Ideal.Quotient.mk P p) = 0 at hx
    rw [hfapp] at hx
    exact hx
  have hindF : AlgebraicIndependent ℂ (fun i : s => F i.1) := by
    have hh := hquot.map' hf
    have hefun : (f ∘ (fun i : s => Ideal.Quotient.mk P (MvPolynomial.X i.1))) =
        fun i : s => F i.1 := by
      funext i
      change f (Ideal.Quotient.mk P (MvPolynomial.X i.1)) = F i.1
      rw [hfapp,MvPolynomial.aeval_X]
    rw [hefun] at hh
    exact hh
  let e : Fin r ≃ s := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin,Fintype.card_coe] using hsr.symm)
  refine ⟨fun i => (e i).1,Subtype.val_injective.comp e.injective,?_⟩
  exact hindF.comp e e.injective

end APSCounting893.Main
end Component_18

section Component_19
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma imageClosure_vanishingIdeal_eq_kernel {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) :
    vanishingIdeal K (imageClosure F) = RingHom.ker (MvPolynomial.aeval F).toRingHom := by
  rw [imageClosure,vanishingIdeal_zClosure,image_vanishingIdeal_eq_kernel]
  rfl

noncomputable def imageCoordinateAlgebraMap {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : CoordinateRing (imageClosure F) →ₐ[K] MvPolynomial (Fin n) K :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval F) (fun p hp => by
    rw [imageClosure_vanishingIdeal_eq_kernel] at hp
    exact hp)

lemma imageCoordinateAlgebraMap_mk {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (p : Polynomials K m) :
    imageCoordinateAlgebraMap F (Ideal.Quotient.mk (vanishingIdeal K (imageClosure F)) p) =
      MvPolynomial.aeval F p := rfl

lemma imageCoordinateAlgebraMap_injective {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : Function.Injective (imageCoordinateAlgebraMap F) := by
  apply (injective_iff_map_eq_zero (imageCoordinateAlgebraMap F).toRingHom).mpr
  intro x hx
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [imageClosure_vanishingIdeal_eq_kernel]
  change MvPolynomial.aeval F p = 0
  change imageCoordinateAlgebraMap F (Ideal.Quotient.mk _ p) = 0 at hx
  rw [imageCoordinateAlgebraMap_mk] at hx
  exact hx

lemma imageCoordinateAlgebraMap_coordinate {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (j : Fin m) :
    imageCoordinateAlgebraMap F (coordinate (imageClosure F) j) = F j := by
  change imageCoordinateAlgebraMap F (Ideal.Quotient.mk _ (MvPolynomial.X j)) = F j
  rw [imageCoordinateAlgebraMap_mk,MvPolynomial.aeval_X]

end APSCounting893.Main
end Component_19

section Component_20
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma prime_quotient_dimension_lower_of_independent {m r : ℕ}
    (P : Ideal (MvPolynomial (Fin (m+1)) ℂ)) [P.IsPrime]
    (v : Fin r → MvPolynomial (Fin (m+1)) ℂ ⧸ P) (hv : AlgebraicIndependent ℂ v) :
    ((r : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin (m+1)) ℂ ⧸ P) := by
  classical
  let A := MvPolynomial (Fin (m+1)) ℂ ⧸ P
  let L := FractionRing A
  letI : Algebra.EssFiniteType A L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors A)
  letI : Algebra.EssFiniteType ℂ L := Algebra.EssFiniteType.comp ℂ A L
  let f : A →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ A L
  have hfield := hv.map' (f := f) (IsFractionRing.injective A L)
  have hcard := hfield.cardinalMk_le_trdeg
  have hfinite := trdeg_lt_aleph0 ℂ L
  have hnat := Cardinal.toNat_le_toNat hcard hfinite
  have hn : r ≤ (Algebra.trdeg ℂ L).toNat := by simpa using hnat
  rw [OAI.PiExponent.FormalInterpolation.mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat P]
  exact_mod_cast hn

end APSCounting893.Main
end Component_20

section Component_21
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma image_dimension_lower_of_independent_coordinates {n m r : ℕ}
    (F : PolynomialMap ℂ n (m+1)) (g : Fin r → Fin (m+1))
    (hF : AlgebraicIndependent ℂ (F ∘ g)) :
    ((r : ℕ∞) : WithBot ℕ∞) ≤ RSCapacity.algDim (imageClosure F) := by
  classical
  let P := vanishingIdeal ℂ (imageClosure F)
  letI : P.IsPrime := irreducibleAffine_ideal_prime (irreducibleAffine_imageClosure F)
  have hcoord : AlgebraicIndependent ℂ (fun i => coordinate (imageClosure F) (g i)) := by
    apply AlgebraicIndependent.of_comp (imageCoordinateAlgebraMap F)
    have he : (imageCoordinateAlgebraMap F ∘ (fun i => coordinate (imageClosure F) (g i))) = F ∘ g := by
      funext i
      exact imageCoordinateAlgebraMap_coordinate F (g i)
    rw [he]
    exact hF
  exact prime_quotient_dimension_lower_of_independent P _ hcoord

end APSCounting893.Main
end Component_21

section Component_22
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma image_dimension_exists_nat {n m : ℕ} (F : PolynomialMap ℂ n (m+1)) :
    ∃ r : ℕ,RSCapacity.algDim (imageClosure F)=((r : ℕ∞) : WithBot ℕ∞) := by
  let P:=vanishingIdeal ℂ (imageClosure F)
  letI : P.IsPrime:=irreducibleAffine_ideal_prime (irreducibleAffine_imageClosure F)
  refine ⟨(Algebra.trdeg ℂ (FractionRing (MvPolynomial (Fin (m+1)) ℂ ⧸ P))).toNat,?_⟩
  exact OAI.PiExponent.FormalInterpolation.mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat P

lemma image_dimension_ge_iff_jacobian_minor {n m r k : ℕ} (F : PolynomialMap ℂ n (m+1))
    (hdim : RSCapacity.algDim (imageClosure F)=((r : ℕ∞) : WithBot ℕ∞)) :
    k≤r ↔ ∃ (o : Fin k → Fin (m+1)) (v : Fin k → Fin n),
      Function.Injective o ∧ Function.Injective v ∧
        (Matrix.of (fun i j => MvPolynomial.pderiv (v j) (F (o i)))).det≠0 := by
  constructor
  · intro hkr
    obtain ⟨g,hg,hind⟩:=exists_independent_image_coordinates F hdim
    let e : Fin k → Fin r := Fin.castLE hkr
    have he : Function.Injective e := by
      intro i j h
      have hv : (e i).val=(e j).val := congrArg Fin.val h
      exact Fin.ext hv
    have hi : AlgebraicIndependent ℂ (fun i => F (g (e i))) := hind.comp e he
    obtain ⟨v,hv,hdet⟩:=(jacobian_independence_criterion _).mp hi
    exact ⟨g ∘ e,v,hg.comp he,hv,hdet⟩
  · rintro ⟨o,v,ho,hv,hdet⟩
    have hi : AlgebraicIndependent ℂ (F ∘ o) := (jacobian_independence_criterion _).mpr ⟨v,hv,hdet⟩
    have hle:=image_dimension_lower_of_independent_coordinates F o hi
    rw [hdim] at hle
    exact_mod_cast hle

lemma image_dimension_le_source_target {n m r : ℕ} (F : PolynomialMap ℂ n (m+1))
    (hdim : RSCapacity.algDim (imageClosure F)=((r : ℕ∞) : WithBot ℕ∞)) : r ≤ n ∧ r ≤ m+1 := by
  obtain ⟨o,v,ho,hv,hdet⟩:=(image_dimension_ge_iff_jacobian_minor F hdim (k:=r)).mp le_rfl
  exact ⟨by simpa using Fintype.card_le_of_injective v hv,by simpa using Fintype.card_le_of_injective o ho⟩

end APSCounting893.Main
end Component_22

section Component_23
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma image_dimension_empty_outputs {n : ℕ} (F : PolynomialMap ℂ n 0) :
    RSCapacity.algDim (imageClosure F)=0 := by
  have hinj : Function.Injective (MvPolynomial.aeval F) :=
    MvPolynomial.aeval_injective_iff_of_isEmpty.mpr (MvPolynomial.C_injective (Fin n) ℂ)
  have hker : RingHom.ker (MvPolynomial.aeval F).toRingHom=⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hinj
  have hI : vanishingIdeal ℂ (imageClosure F)=⊥ := by
    rw [imageClosure_vanishingIdeal_eq_kernel]
    exact hker
  unfold RSCapacity.algDim
  rw [hI]
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),ringKrullDim_mvPolynomial_of_isEmpty,
    ringKrullDim_eq_zero_of_field]

end APSCounting893.Main
end Component_23

section Component_24
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma image_dimension_minor_characterization {n m : ℕ} (F : PolynomialMap ℂ n m) :
    ∃ r : ℕ,RSCapacity.algDim (imageClosure F)=((r : ℕ∞) : WithBot ℕ∞) ∧
      ∀ k : ℕ,k≤r ↔ ∃ (o : Fin k → Fin m) (v : Fin k → Fin n),
        Function.Injective o ∧ Function.Injective v ∧
          (Matrix.of (fun i j => MvPolynomial.pderiv (v j) (F (o i)))).det≠0 := by
  cases m with
  | zero =>
    refine ⟨0,by simpa using image_dimension_empty_outputs F,?_⟩
    intro k
    constructor
    · intro hk
      have hk0 : k=0 := by omega
      subst k
      refine ⟨Fin.elim0,Fin.elim0,?_,?_,?_⟩
      · intro i;exact Fin.elim0 i
      · intro i;exact Fin.elim0 i
      · simpa using (one_ne_zero : (1 : MvPolynomial (Fin n) ℂ)≠0)
    · rintro ⟨o,v,ho,hv,hdet⟩
      simpa using Fintype.card_le_of_injective o ho
  | succ m =>
    obtain ⟨r,hr⟩:=image_dimension_exists_nat F
    exact ⟨r,hr,fun k => image_dimension_ge_iff_jacobian_minor F hr⟩

end APSCounting893.Main
end Component_24

section Component_25
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma circuit_image_dimension_integer_minors {n : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) :
    ∃ r : ℕ,RSCapacity.algDim (imageClosure (rationalComplexPolynomials C))=((r : ℕ∞) : WithBot ℕ∞) ∧
      ∀ k : ℕ,k≤r ↔ ∃ (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n),
        Function.Injective o ∧ Function.Injective v ∧ circuitJacobianIntegerMinor C o v≠0 := by
  obtain ⟨r,hr,hminor⟩:=image_dimension_minor_characterization (rationalComplexPolynomials C)
  refine ⟨r,hr,?_⟩
  intro k
  constructor
  · intro hkr
    obtain ⟨o,v,ho,hv,hdet⟩:=(hminor k).mp hkr
    exact ⟨o,v,ho,hv,(circuitJacobianIntegerMinor_ne_zero_iff_complex C hvalid o v).mpr hdet⟩
  · rintro ⟨o,v,ho,hv,hdet⟩
    exact (hminor k).mpr ⟨o,v,ho,hv,(circuitJacobianIntegerMinor_ne_zero_iff_complex C hvalid o v).mp hdet⟩

end APSCounting893.Main
end Component_25

section Component_26

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma totalDegree_pderiv_lt {K : Type*} [CommRing K] [IsDomain K] {ι : Type*}
    (p : MvPolynomial (ι) K) (i : ι) (h : pderiv i p ≠ 0) :
    (pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hs (e : ι →₀ ℕ) (he : e ∈ (pderiv i p).support) :
      e.sum (fun _ k => k) + 1 ≤ p.totalDegree := by
    have hcoef := MvPolynomial.mem_support_iff.mp he
    rw [MvPolynomial.coeff_pderiv] at hcoef
    have hq : p.coeff (e + Finsupp.single i 1) ≠ 0 :=
      fun hz => hcoef (by rw [hz, zero_mul])
    have hh := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hq)
    have heq : (e + Finsupp.single i 1).sum (fun _ k => k) = e.sum (fun _ k => k) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp
    rwa [heq] at hh
  have hd : 0 < p.totalDegree := by
    obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr h
    have hh := hs e he
    omega
  have hb : (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
    rw [MvPolynomial.totalDegree]
    apply Finset.sup_le
    intro e he
    have hh := hs e he
    omega
  omega

lemma eq_C_of_forall_pderiv_zero {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {ι : Type*}
    (p : MvPolynomial (ι) K) (hp : ∀ i, pderiv i p = 0) :
    p = MvPolynomial.C (p.coeff 0) := by
  classical
  ext e
  by_cases he : e = 0
  · subst e
    simp
  have hi : ∃ i, e i ≠ 0 := by
    by_contra h
    push Not at h
    exact he (Finsupp.ext h)
  obtain ⟨i, hi⟩ := hi
  have hle : Finsupp.single i 1 ≤ e := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
  have hre : e - Finsupp.single i 1 + Finsupp.single i 1 = e := tsub_add_cancel_of_le hle
  have hc := congrArg (MvPolynomial.coeff (e - Finsupp.single i 1)) (hp i)
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_zero, hre] at hc
  have hval : (e - Finsupp.single i 1 : ι →₀ ℕ) i + 1 = e i := by
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  have hn : (((e - Finsupp.single i 1 : ι →₀ ℕ) i : ℕ) : K) + 1 ≠ 0 := by
    have hh : (((e - Finsupp.single i 1 : ι →₀ ℕ) i + 1 : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega)
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hpc : p.coeff e = 0 := (mul_eq_zero.mp hc).resolve_right hn
  simp [MvPolynomial.coeff_C, Ne.symm he, hpc]

lemma pderiv_aeval_chain {K : Type*} [CommRing K] [IsDomain K] {ι κ : Type*} [Fintype ι]
    (F : ι → MvPolynomial (κ) K) (p : MvPolynomial (ι) K) (j : κ) :
    pderiv j (MvPolynomial.aeval F p) =
      ∑ i, MvPolynomial.aeval F (pderiv i p) * pderiv j (F i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.aeval_C, MvPolynomial.pderiv_C]
  | add p q hp hq =>
    simp only [map_add, hp, hq, Finset.sum_add_distrib, add_mul]
  | mul_X p k hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.pderiv_mul, hp,
      map_add, MvPolynomial.pderiv_X, map_mul, MvPolynomial.aeval_X]
    simp only [add_mul, Finset.sum_add_distrib]
    have h1 : (∑ i, MvPolynomial.aeval F (pderiv i p) * pderiv j (F i)) * F k =
        ∑ i, MvPolynomial.aeval F (pderiv i p) * F k * pderiv j (F i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [h1]
    congr 1
    simp [Pi.single_apply, Finset.mul_sum, mul_assoc]

end APSCounting893.Main
end Component_26

section Component_27
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma polynomial_pderiv_degree_le {n : ℕ} (j : Fin n) (p : MvPolynomial (Fin n) ℤ) :
    (MvPolynomial.pderiv j p).totalDegree≤p.totalDegree := by
  by_cases hz : MvPolynomial.pderiv j p=0
  · simp only [hz,MvPolynomial.totalDegree_zero,Nat.zero_le]
  · exact (totalDegree_pderiv_lt p j hz).le

lemma IntegerPolynomialPair.derivative_degree_bound {n : ℕ} (j : Fin n) (p : IntegerPolynomialPair n) :
    (p.derivative j).degree≤2*p.degree := by
  have hp1 : p.1.totalDegree≤p.degree := le_max_left _ _
  have hp2 : p.2.totalDegree≤p.degree := le_max_right _ _
  have hd1 : (MvPolynomial.pderiv j p.1).totalDegree≤p.degree := (polynomial_pderiv_degree_le j p.1).trans hp1
  have hd2 : (MvPolynomial.pderiv j p.2).totalDegree≤p.degree := (polynomial_pderiv_degree_le j p.2).trans hp2
  change max (MvPolynomial.pderiv j p.1*p.2-p.1*MvPolynomial.pderiv j p.2).totalDegree (p.2^2).totalDegree≤_
  apply max_le
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  · exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 hp2)

end APSCounting893.Main
end Component_27

section Component_28
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace APSCounting893.Main

noncomputable def polynomialJetHeight {n : ℕ} (x : Fin n → ℤ) (j : Fin n) (p : MvPolynomial (Fin n) ℤ) : ℕ :=
  max (MvPolynomial.eval x p).natAbs (MvPolynomial.eval x (MvPolynomial.pderiv j p)).natAbs

lemma polynomialJetHeight_add {n : ℕ} (x : Fin n → ℤ) (j : Fin n) (p q : MvPolynomial (Fin n) ℤ) :
    polynomialJetHeight x j (p+q)≤polynomialJetHeight x j p+polynomialJetHeight x j q := by
  unfold polynomialJetHeight
  simp only [map_add]
  apply max_le
  · exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add (le_max_right _ _) (le_max_right _ _))

lemma polynomialJetHeight_neg {n : ℕ} (x : Fin n → ℤ) (j : Fin n) (p : MvPolynomial (Fin n) ℤ) :
    polynomialJetHeight x j (-p)=polynomialJetHeight x j p := by
  simp only [polynomialJetHeight,map_neg,Int.natAbs_neg]

lemma polynomialJetHeight_sub {n : ℕ} (x : Fin n → ℤ) (j : Fin n) (p q : MvPolynomial (Fin n) ℤ) :
    polynomialJetHeight x j (p-q)≤polynomialJetHeight x j p+polynomialJetHeight x j q := by
  simpa only [sub_eq_add_neg,polynomialJetHeight_neg] using polynomialJetHeight_add x j p (-q)

lemma polynomialJetHeight_mul {n : ℕ} (x : Fin n → ℤ) (j : Fin n) (p q : MvPolynomial (Fin n) ℤ) :
    polynomialJetHeight x j (p*q)≤2*polynomialJetHeight x j p*polynomialJetHeight x j q := by
  have hp1:=le_max_left (MvPolynomial.eval x p).natAbs (MvPolynomial.eval x (MvPolynomial.pderiv j p)).natAbs
  have hp2:=le_max_right (MvPolynomial.eval x p).natAbs (MvPolynomial.eval x (MvPolynomial.pderiv j p)).natAbs
  have hq1:=le_max_left (MvPolynomial.eval x q).natAbs (MvPolynomial.eval x (MvPolynomial.pderiv j q)).natAbs
  have hq2:=le_max_right (MvPolynomial.eval x q).natAbs (MvPolynomial.eval x (MvPolynomial.pderiv j q)).natAbs
  unfold polynomialJetHeight
  simp only [MvPolynomial.pderiv_mul,map_add,map_mul,Int.natAbs_mul]
  apply max_le
  · exact (Nat.mul_le_mul hp1 hq1).trans (Nat.mul_le_mul_right _ (by omega))
  · apply (Int.natAbs_add_le _ _).trans
    simp only [Int.natAbs_mul]
    have h1:=Nat.mul_le_mul hp1 hq2
    have h2:=Nat.mul_le_mul hp2 hq1
    nlinarith

end APSCounting893.Main
end Component_28

section Component_29
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
namespace IntegerPolynomialPair

noncomputable def jetHeight {n : ℕ} (x : Fin n → ℤ) (j : Fin n) (p : IntegerPolynomialPair n) : ℕ :=
  max (polynomialJetHeight x j p.1) (polynomialJetHeight x j p.2)

lemma jetHeight_add {n : ℕ} (x : Fin n → ℤ) (j : Fin n) (p q : IntegerPolynomialPair n) :
    (p.add q).jetHeight x j≤4*p.jetHeight x j*q.jetHeight x j := by
  have hp1:=le_max_left (polynomialJetHeight x j p.1) (polynomialJetHeight x j p.2)
  have hp2:=le_max_right (polynomialJetHeight x j p.1) (polynomialJetHeight x j p.2)
  have hq1:=le_max_left (polynomialJetHeight x j q.1) (polynomialJetHeight x j q.2)
  have hq2:=le_max_right (polynomialJetHeight x j q.1) (polynomialJetHeight x j q.2)
  change max (polynomialJetHeight x j (p.1*q.2+q.1*p.2)) (polynomialJetHeight x j (p.2*q.2))≤_
  apply max_le
  · calc
      _ ≤ polynomialJetHeight x j (p.1*q.2)+polynomialJetHeight x j (q.1*p.2) := polynomialJetHeight_add _ _ _ _
      _ ≤ 2*p.jetHeight x j*q.jetHeight x j+2*q.jetHeight x j*p.jetHeight x j :=
        Nat.add_le_add ((polynomialJetHeight_mul _ _ _ _).trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hp1) hq2))
          ((polynomialJetHeight_mul _ _ _ _).trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hq1) hp2))
      _ = _ := by ring
  · exact (polynomialJetHeight_mul _ _ _ _).trans
      ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 hp2) hq2).trans
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 2≤4))))

lemma jetHeight_sub {n : ℕ} (x : Fin n → ℤ) (j : Fin n) (p q : IntegerPolynomialPair n) :
    (p.sub q).jetHeight x j≤4*p.jetHeight x j*q.jetHeight x j := by
  have hp1:=le_max_left (polynomialJetHeight x j p.1) (polynomialJetHeight x j p.2)
  have hp2:=le_max_right (polynomialJetHeight x j p.1) (polynomialJetHeight x j p.2)
  have hq1:=le_max_left (polynomialJetHeight x j q.1) (polynomialJetHeight x j q.2)
  have hq2:=le_max_right (polynomialJetHeight x j q.1) (polynomialJetHeight x j q.2)
  change max (polynomialJetHeight x j (p.1*q.2-q.1*p.2)) (polynomialJetHeight x j (p.2*q.2))≤_
  apply max_le
  · calc
      _ ≤ polynomialJetHeight x j (p.1*q.2)+polynomialJetHeight x j (q.1*p.2) := polynomialJetHeight_sub _ _ _ _
      _ ≤ 2*p.jetHeight x j*q.jetHeight x j+2*q.jetHeight x j*p.jetHeight x j :=
        Nat.add_le_add ((polynomialJetHeight_mul _ _ _ _).trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hp1) hq2))
          ((polynomialJetHeight_mul _ _ _ _).trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hq1) hp2))
      _ = _ := by ring
  · exact (polynomialJetHeight_mul _ _ _ _).trans
      ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 hp2) hq2).trans
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 2≤4))))

lemma jetHeight_mul {n : ℕ} (x : Fin n → ℤ) (j : Fin n) (p q : IntegerPolynomialPair n) :
    (p.mul q).jetHeight x j≤2*p.jetHeight x j*q.jetHeight x j := by
  change max (polynomialJetHeight x j (p.1*q.1)) (polynomialJetHeight x j (p.2*q.2))≤_
  exact max_le ((polynomialJetHeight_mul _ _ _ _).trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (le_max_left _ _)) (le_max_left _ _)))
    ((polynomialJetHeight_mul _ _ _ _).trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (le_max_right _ _)) (le_max_right _ _)))

lemma jetHeight_div {n : ℕ} (x : Fin n → ℤ) (j : Fin n) (p q : IntegerPolynomialPair n) :
    (p.div q).jetHeight x j≤2*p.jetHeight x j*q.jetHeight x j := by
  change max (polynomialJetHeight x j (p.1*q.2)) (polynomialJetHeight x j (p.2*q.1))≤_
  exact max_le ((polynomialJetHeight_mul _ _ _ _).trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (le_max_left _ _)) (le_max_right _ _)))
    ((polynomialJetHeight_mul _ _ _ _).trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (le_max_right _ _)) (le_max_left _ _)))

end IntegerPolynomialPair
end APSCounting893.Main
end Component_29

section Component_30
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
namespace IntegerPolynomialPair

noncomputable def evalHeight {n : ℕ} (x : Fin n → ℤ) (p : IntegerPolynomialPair n) : ℕ :=
  max (MvPolynomial.eval x p.1).natAbs (MvPolynomial.eval x p.2).natAbs

lemma evalHeight_add {n : ℕ} (x : Fin n → ℤ) (p q : IntegerPolynomialPair n) :
    (p.add q).evalHeight x ≤ 2*p.evalHeight x*q.evalHeight x := by
  have hp1:=le_max_left (MvPolynomial.eval x p.1).natAbs (MvPolynomial.eval x p.2).natAbs
  have hp2:=le_max_right (MvPolynomial.eval x p.1).natAbs (MvPolynomial.eval x p.2).natAbs
  have hq1:=le_max_left (MvPolynomial.eval x q.1).natAbs (MvPolynomial.eval x q.2).natAbs
  have hq2:=le_max_right (MvPolynomial.eval x q.1).natAbs (MvPolynomial.eval x q.2).natAbs
  have hn:=Int.natAbs_add_le (MvPolynomial.eval x p.1*MvPolynomial.eval x q.2)
    (MvPolynomial.eval x q.1*MvPolynomial.eval x p.2)
  simp only [Int.natAbs_mul] at hn
  change max (MvPolynomial.eval x (p.1*q.2+q.1*p.2)).natAbs (MvPolynomial.eval x (p.2*q.2)).natAbs ≤ _
  simp only [map_add,map_mul,Int.natAbs_mul]
  apply max_le
  · apply hn.trans
    change _ ≤ 2*max (MvPolynomial.eval x p.1).natAbs (MvPolynomial.eval x p.2).natAbs*
      max (MvPolynomial.eval x q.1).natAbs (MvPolynomial.eval x q.2).natAbs
    nlinarith [Nat.mul_le_mul hp1 hq2,Nat.mul_le_mul hq1 hp2]
  · change _ ≤ 2*max (MvPolynomial.eval x p.1).natAbs (MvPolynomial.eval x p.2).natAbs*
      max (MvPolynomial.eval x q.1).natAbs (MvPolynomial.eval x q.2).natAbs
    apply (Nat.mul_le_mul hp2 hq2).trans
    exact Nat.mul_le_mul_right _ (by omega)

lemma evalHeight_sub {n : ℕ} (x : Fin n → ℤ) (p q : IntegerPolynomialPair n) :
    (p.sub q).evalHeight x ≤ 2*p.evalHeight x*q.evalHeight x := by
  have hp1:=le_max_left (MvPolynomial.eval x p.1).natAbs (MvPolynomial.eval x p.2).natAbs
  have hp2:=le_max_right (MvPolynomial.eval x p.1).natAbs (MvPolynomial.eval x p.2).natAbs
  have hq1:=le_max_left (MvPolynomial.eval x q.1).natAbs (MvPolynomial.eval x q.2).natAbs
  have hq2:=le_max_right (MvPolynomial.eval x q.1).natAbs (MvPolynomial.eval x q.2).natAbs
  have hn:=Int.natAbs_add_le (MvPolynomial.eval x p.1*MvPolynomial.eval x q.2)
    (-(MvPolynomial.eval x q.1*MvPolynomial.eval x p.2))
  simp only [Int.natAbs_neg,Int.natAbs_mul] at hn
  change max (MvPolynomial.eval x (p.1*q.2-q.1*p.2)).natAbs (MvPolynomial.eval x (p.2*q.2)).natAbs ≤ _
  simp only [map_sub,map_mul,Int.natAbs_mul]
  apply max_le
  · apply hn.trans
    change _ ≤ 2*max (MvPolynomial.eval x p.1).natAbs (MvPolynomial.eval x p.2).natAbs*
      max (MvPolynomial.eval x q.1).natAbs (MvPolynomial.eval x q.2).natAbs
    nlinarith [Nat.mul_le_mul hp1 hq2,Nat.mul_le_mul hq1 hp2]
  · change _ ≤ 2*max (MvPolynomial.eval x p.1).natAbs (MvPolynomial.eval x p.2).natAbs*
      max (MvPolynomial.eval x q.1).natAbs (MvPolynomial.eval x q.2).natAbs
    apply (Nat.mul_le_mul hp2 hq2).trans
    exact Nat.mul_le_mul_right _ (by omega)

lemma evalHeight_mul {n : ℕ} (x : Fin n → ℤ) (p q : IntegerPolynomialPair n) :
    (p.mul q).evalHeight x ≤ p.evalHeight x*q.evalHeight x := by
  change max (MvPolynomial.eval x (p.1*q.1)).natAbs (MvPolynomial.eval x (p.2*q.2)).natAbs ≤ _
  simp only [map_mul,Int.natAbs_mul]
  exact max_le (Nat.mul_le_mul (le_max_left _ _) (le_max_left _ _))
    (Nat.mul_le_mul (le_max_right _ _) (le_max_right _ _))

lemma evalHeight_div {n : ℕ} (x : Fin n → ℤ) (p q : IntegerPolynomialPair n) :
    (p.div q).evalHeight x ≤ p.evalHeight x*q.evalHeight x := by
  change max (MvPolynomial.eval x (p.1*q.2)).natAbs (MvPolynomial.eval x (p.2*q.1)).natAbs ≤ _
  simp only [map_mul,Int.natAbs_mul]
  exact max_le (Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _))
    (Nat.mul_le_mul (le_max_right _ _) (le_max_left _ _))

end IntegerPolynomialPair
end APSCounting893.Main
end Component_30

section Component_31
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
namespace IntegerPolynomialPair

lemma derivative_evalHeight_bound {n : ℕ} (x : Fin n → ℤ) (j : Fin n) (p : IntegerPolynomialPair n) :
    (p.derivative j).evalHeight x≤2*p.jetHeight x j*p.jetHeight x j := by
  let J:=p.jetHeight x j
  have hN : (MvPolynomial.eval x p.1).natAbs≤J :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hD : (MvPolynomial.eval x p.2).natAbs≤J :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hN' : (MvPolynomial.eval x (MvPolynomial.pderiv j p.1)).natAbs≤J :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hD' : (MvPolynomial.eval x (MvPolynomial.pderiv j p.2)).natAbs≤J :=
    (le_max_right _ _).trans (le_max_right _ _)
  change max (MvPolynomial.eval x (MvPolynomial.pderiv j p.1*p.2-p.1*MvPolynomial.pderiv j p.2)).natAbs
    (MvPolynomial.eval x (p.2^2)).natAbs≤2*J*J
  rw [pow_two]
  simp only [map_sub,map_mul,Int.natAbs_mul]
  apply max_le
  · have hh:=Int.natAbs_add_le (MvPolynomial.eval x (MvPolynomial.pderiv j p.1)*MvPolynomial.eval x p.2)
      (-(MvPolynomial.eval x p.1*MvPolynomial.eval x (MvPolynomial.pderiv j p.2)))
    simp only [Int.natAbs_neg,Int.natAbs_mul] at hh
    apply hh.trans
    have h1:=Nat.mul_le_mul hN' hD
    have h2:=Nat.mul_le_mul hN hD'
    nlinarith
  · exact (Nat.mul_le_mul hD hD).trans (Nat.mul_le_mul_right _ (by omega))

end IntegerPolynomialPair
end APSCounting893.Main
end Component_31

section Component_32
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace APSCounting893.Main

lemma polynomial_matrix_det_degree {K : Type} [CommRing K] {σ : Type} {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (MvPolynomial σ K)) (D : ℕ)
    (hA : ∀ i j,(A i j).totalDegree≤D) : A.det.totalDegree≤r*D := by
  classical
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e he
  change (((Equiv.Perm.sign e : ℤ) • ∏ i,A (e i) i)).totalDegree≤_
  apply (MvPolynomial.totalDegree_smul_le _ _).trans
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    (∑ i : Fin r,(A (e i) i).totalDegree) ≤ ∑ _i : Fin r,D := Finset.sum_le_sum (fun i hi => hA _ _)
    _ = r*D := by simp

end APSCounting893.Main
end Component_32

section Component_33
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma clearedIntegerMatrix_degree_bound {n r : ℕ}
    (A : Matrix (Fin r) (Fin r) (IntegerPolynomialPair n)) (D : ℕ)
    (hA : ∀ i j,(A i j).degree≤D) (i j : Fin r) :
    (clearedIntegerMatrix A i j).totalDegree≤(r+1)*D := by
  classical
  have hnum : (A i j).1.totalDegree≤D := (le_max_left _ _).trans (hA i j)
  have hden (k : Fin r) : (A i k).2.totalDegree≤D := (le_max_right _ _).trans (hA i k)
  have hprod : (∏ k ∈ Finset.univ.erase j,(A i k).2).totalDegree≤r*D := by
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    calc
      (∑ k ∈ Finset.univ.erase j,(A i k).2.totalDegree) ≤ ∑ _k ∈ Finset.univ.erase j,D :=
        Finset.sum_le_sum (fun k hk => hden k)
      _ ≤ r*D := by simpa using Nat.mul_le_mul_right D (Nat.sub_le r 1)
  apply (MvPolynomial.totalDegree_mul _ _).trans
  calc
    _ ≤ D+r*D := Nat.add_le_add hnum hprod
    _ = (r+1)*D := by ring

lemma clearedIntegerMatrix_det_degree_bound {n r : ℕ}
    (A : Matrix (Fin r) (Fin r) (IntegerPolynomialPair n)) (D : ℕ)
    (hA : ∀ i j,(A i j).degree≤D) :
    (clearedIntegerMatrix A).det.totalDegree≤r*((r+1)*D) :=
  polynomial_matrix_det_degree _ _ (clearedIntegerMatrix_degree_bound A D hA)

end APSCounting893.Main
end Component_33

section Component_34
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace APSCounting893.Main

lemma integer_matrix_det_natAbs_bound {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (H : ℕ)
    (hA : ∀ i j,(A i j).natAbs≤H) : A.det.natAbs≤r.factorial*H^r := by
  classical
  rw [Matrix.det_apply]
  apply (Int.natAbs_sum_le _ _).trans
  have hterm (e : Equiv.Perm (Fin r)) :
      (Equiv.Perm.sign e • ∏ i,A (e i) i).natAbs≤H^r := by
    change (((Equiv.Perm.sign e : ℤ)*∏ i,A (e i) i)).natAbs≤_
    rw [Int.natAbs_mul]
    have hs : (Equiv.Perm.sign e : ℤ).natAbs=1 :=
      Int.isUnit_iff_natAbs_eq.mp (Equiv.Perm.sign e).isUnit
    rw [hs,one_mul]
    have hprod : (∏ i,A (e i) i).natAbs=∏ i,(A (e i) i).natAbs :=
      map_prod Int.natAbsHom _ _
    rw [hprod]
    calc
      (∏ i : Fin r,(A (e i) i).natAbs) ≤ ∏ _i : Fin r,H := Finset.prod_le_prod (fun i hi => Nat.zero_le _) (fun i hi => hA _ _)
      _ = H^r := by simp
  calc
    (∑ e : Equiv.Perm (Fin r),(Equiv.Perm.sign e • ∏ i,A (e i) i).natAbs) ≤
      ∑ _e : Equiv.Perm (Fin r),H^r := Finset.sum_le_sum (fun e he => hterm e)
    _ = r.factorial*H^r := by simp [Fintype.card_perm]

end APSCounting893.Main
end Component_34

section Component_35
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma clearedIntegerMatrix_eval_bound {n r : ℕ} (x : Fin n → ℤ)
    (A : Matrix (Fin r) (Fin r) (IntegerPolynomialPair n)) (H : ℕ) (hH : 1≤H)
    (hA : ∀ i j,(A i j).evalHeight x≤H) (i j : Fin r) :
    (MvPolynomial.eval x (clearedIntegerMatrix A i j)).natAbs≤H^(r+1) := by
  classical
  have hnum : (MvPolynomial.eval x (A i j).1).natAbs≤H := (le_max_left _ _).trans (hA i j)
  have hden (k : Fin r) : (MvPolynomial.eval x (A i k).2).natAbs≤H := (le_max_right _ _).trans (hA i k)
  have hprod : (∏ k ∈ Finset.univ.erase j,(MvPolynomial.eval x (A i k).2).natAbs)≤H^r := by
    calc
      _ ≤ ∏ _k ∈ Finset.univ.erase j,H := Finset.prod_le_prod (fun k hk => Nat.zero_le _) (fun k hk => hden k)
      _ ≤ H^r := by
        simp only [Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ,Fintype.card_fin]
        exact Nat.pow_le_pow_right hH (Nat.sub_le r 1)
  simp only [clearedIntegerMatrix,map_mul,map_prod,Int.natAbs_mul]
  have heq : (∏ k ∈ Finset.univ.erase j,MvPolynomial.eval x (A i k).2).natAbs=
      ∏ k ∈ Finset.univ.erase j,(MvPolynomial.eval x (A i k).2).natAbs := map_prod Int.natAbsHom _ _
  rw [heq]
  simpa only [pow_succ,Nat.mul_comm] using Nat.mul_le_mul hnum hprod

lemma clearedIntegerMatrix_det_eval_bound {n r : ℕ} (x : Fin n → ℤ)
    (A : Matrix (Fin r) (Fin r) (IntegerPolynomialPair n)) (H : ℕ) (hH : 1≤H)
    (hA : ∀ i j,(A i j).evalHeight x≤H) :
    (MvPolynomial.eval x (clearedIntegerMatrix A).det).natAbs≤r.factorial*(H^(r+1))^r := by
  have hh:=integer_matrix_det_natAbs_bound
    (Matrix.of fun i j => MvPolynomial.eval x (clearedIntegerMatrix A i j)) (H^(r+1))
    (clearedIntegerMatrix_eval_bound x A H hH hA)
  have hm:=RingHom.map_det (MvPolynomial.eval x) (clearedIntegerMatrix A)
  exact hm ▸ hh

end APSCounting893.Main
end Component_35

section Component_36
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma integerGateValue_jetHeight_bound {n : ℕ} (x : Fin n → ℤ) (j : Fin n)
    (prior : List (IntegerPolynomialPair n)) (H M : ℕ) (hH : 1≤H) (hHM : H≤M)
    (hvar : ∀ i,(x i).natAbs≤H) (g : ArithmeticGate n)
    (hconst : match g with
      | .constant cs => (cs.headD 0).num.natAbs≤H ∧ (cs.headD 0).den≤H
      | _ => True)
    (hprior : ∀ p ∈ prior,p.jetHeight x j≤M)
    (p : IntegerPolynomialPair n) (hp : integerGateValue prior g=some p) :
    p.jetHeight x j≤4*M*M := by
  cases g with
  | «variable» i =>
    simp only [integerGateValue,Option.some.injEq] at hp
    subst p
    have hi : polynomialJetHeight x j (MvPolynomial.X i)≤H := by
      unfold polynomialJetHeight
      rw [MvPolynomial.eval_X,MvPolynomial.pderiv_X]
      by_cases hji : j=i
      · subst i
        simpa using max_le (hvar j) hH
      · simpa [Pi.single_apply,hji,Ne.symm hji] using hvar i
    have h1 : polynomialJetHeight x j (1 : MvPolynomial (Fin n) ℤ)≤H := by
      simpa [polynomialJetHeight] using hH
    apply (max_le hi h1).trans
    have hm : 1≤M := hH.trans hHM
    nlinarith
  | «constant» cs =>
    simp only [integerGateValue,Option.some.injEq] at hp
    subst p
    change max (polynomialJetHeight x j (MvPolynomial.C (cs.headD 0).num))
      (polynomialJetHeight x j (MvPolynomial.C ((cs.headD 0).den : ℤ)))≤_
    simp only [polynomialJetHeight,MvPolynomial.eval_C,MvPolynomial.pderiv_C,map_zero,
      Int.natAbs_zero,Nat.max_zero,Int.natAbs_natCast]
    apply (max_le hconst.1 hconst.2).trans
    have hm : 1≤M := hH.trans hHM
    nlinarith
  | add a b | sub a b | mul a b | div a b =>
    cases ha : prior[a]? <;> cases hb : prior[b]? <;> simp [integerGateValue,ha,hb] at hp
    subst p
    rename_i p q
    have hp':=hprior p (List.mem_of_getElem? ha)
    have hq':=hprior q (List.mem_of_getElem? hb)
    first
    | exact (IntegerPolynomialPair.jetHeight_add x j p q).trans
        (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hp') hq')
    | exact (IntegerPolynomialPair.jetHeight_sub x j p q).trans
        (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hp') hq')
    | exact (IntegerPolynomialPair.jetHeight_mul x j p q).trans
        ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 hp') hq').trans
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 2≤4))))
    | exact (IntegerPolynomialPair.jetHeight_div x j p q).trans
        ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 hp') hq').trans
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 2≤4))))

end APSCounting893.Main
end Component_36

section Component_37
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma integerCircuitValues_jetHeight_bound {n : ℕ} (C : ArithmeticCircuit n) (x : Fin n → ℤ) (j : Fin n)
    (H : ℕ) (hH : 1≤H) (hvar : ∀ i,(x i).natAbs≤H)
    (hconst : ∀ g ∈ C.gates,match g with
      | .constant cs => (cs.headD 0).num.natAbs≤H ∧ (cs.headD 0).den≤H
      | _ => True)
    (ps : List (IntegerPolynomialPair n)) (hps : integerCircuitValues C=some ps) :
    ∀ p ∈ ps,p.jetHeight x j≤(4*H)^(2^C.gates.length) := by
  let step := fun (acc : Option (List (IntegerPolynomialPair n))) (g : ArithmeticGate n) => do
    let prior ← acc
    let p ← integerGateValue prior g
    return prior++[p]
  have hnone (gs : List (ArithmeticGate n)) : gs.foldl step none=none := by
    induction gs with
    | nil => rfl
    | cons g gs ih => exact ih
  have hfold (gs : List (ArithmeticGate n))
      (hcs : ∀ g ∈ gs,match g with
        | .constant cs => (cs.headD 0).num.natAbs≤H ∧ (cs.headD 0).den≤H
        | _ => True)
      (prior : List (IntegerPolynomialPair n)) (M : ℕ) (hHM : H≤M)
      (hprior : ∀ p ∈ prior,p.jetHeight x j≤M) (out : List (IntegerPolynomialPair n))
      (hout : gs.foldl step (some prior)=some out) :
      ∀ p ∈ out,p.jetHeight x j≤(4*M)^(2^gs.length) := by
    induction gs generalizing prior M out with
    | nil =>
      have he : prior=out := Option.some.inj hout
      subst out
      intro p hp
      simpa only [List.length_nil,pow_zero,pow_one] using (hprior p hp).trans (by omega : M≤4*M)
    | cons g gs ih =>
      rw [List.foldl_cons] at hout
      change gs.foldl step ((integerGateValue prior g).bind (fun p => some (prior++[p])))=some out at hout
      cases hg : integerGateValue prior g with
      | none => simp only [hg,Option.bind_none,hnone] at hout;cases hout
      | some q =>
        have hqd:=integerGateValue_jetHeight_bound x j prior H M hH hHM hvar g (hcs g (by simp)) hprior q hg
        have hM : 1≤M := hH.trans hHM
        have hM' : M≤4*M*M := by nlinarith
        have hnew : ∀ p ∈ prior++[q],p.jetHeight x j≤4*M*M := by
          intro p hp
          rcases List.mem_append.mp hp with hp|hp
          · exact (hprior p hp).trans hM'
          · have he : p=q := by simpa using hp
            simpa only [he] using hqd
        have hh : gs.foldl step (some (prior++[q]))=some out := by simpa only [hg,Option.bind_some] using hout
        intro p hp
        have hb:=ih (fun g hg => hcs g (by simp [hg])) (prior++[q]) (4*M*M)
          (hHM.trans hM') hnew out hh p hp
        have he : (4*(4*M*M))^(2^gs.length)=(4*M)^(2^(g::gs).length) := by
          rw [show 4*(4*M*M)=(4*M)^2 by ring,←pow_mul]
          simp [pow_succ,Nat.mul_comm]
        rwa [he] at hb
  exact hfold C.gates hconst [] H le_rfl (by simp) ps hps

end APSCounting893.Main
end Component_37

section Component_38
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma integerCircuitOutput_mem_values {n : ℕ} (C : ArithmeticCircuit n) (hvalid : ValidCircuit .rational C)
    (ps : List (IntegerPolynomialPair n)) (hps : integerCircuitValues C=some ps) (j : Fin C.outputs.length) :
    integerCircuitOutput C j∈ps := by
  obtain ⟨values,hv,hout⟩:=hvalid.2
  obtain ⟨qs,hqs,hden,hmap⟩:=integerCircuitValues_of_success C values hv
  have heq : qs=ps := Option.some.inj (hqs.symm.trans hps)
  subst qs
  obtain ⟨v,f,hget,hf⟩:=hout C.outputs[j] (List.getElem_mem _)
  rw [←hmap,List.getElem?_map] at hget
  cases hp : ps[C.outputs[j]]? with
  | none => simp only [hp,Option.map_none] at hget;cases hget
  | some p =>
    have hlookup : integerCircuitOutput C j=p := by simp only [integerCircuitOutput,hps,Option.getD_some,hp]
    rw [hlookup]
    exact List.mem_of_getElem? hp

lemma integerCircuitOutput_jetHeight_bound {n : ℕ} (C : ArithmeticCircuit n) (hvalid : ValidCircuit .rational C)
    (x : Fin n → ℤ) (j : Fin n) (H : ℕ) (hH : 1≤H) (hvar : ∀ i,(x i).natAbs≤H)
    (hconst : ∀ g ∈ C.gates,match g with
      | .constant cs => (cs.headD 0).num.natAbs≤H ∧ (cs.headD 0).den≤H
      | _ => True) (o : Fin C.outputs.length) :
    (integerCircuitOutput C o).jetHeight x j≤(4*H)^(2^C.gates.length) := by
  obtain ⟨values,hv,hout⟩:=hvalid.2
  obtain ⟨ps,hps,hden,hmap⟩:=integerCircuitValues_of_success C values hv
  exact integerCircuitValues_jetHeight_bound C x j H hH hvar hconst ps hps _
    (integerCircuitOutput_mem_values C hvalid ps hps o)

end APSCounting893.Main
end Component_38

section Component_39
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma circuitJacobianIntegerMinor_degree_bound {n k : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) :
    (circuitJacobianIntegerMinor C o v).totalDegree≤k*((k+1)*(2*2^C.gates.length)) := by
  apply clearedIntegerMatrix_det_degree_bound
  intro i j
  exact ((integerCircuitOutput C (o i)).derivative_degree_bound (v j)).trans
    (Nat.mul_le_mul_left 2 (integerCircuitOutput_degree_bound C hvalid (o i)))

lemma circuitJacobianIntegerMinor_eval_bound {n k : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n)
    (x : Fin n → ℤ) (H : ℕ) (hH : 1≤H) (hvar : ∀ i,(x i).natAbs≤H)
    (hconst : ∀ g ∈ C.gates,match g with
      | .constant cs => (cs.headD 0).num.natAbs≤H ∧ (cs.headD 0).den≤H
      | _ => True) :
    (MvPolynomial.eval x (circuitJacobianIntegerMinor C o v)).natAbs≤
      k.factorial*((2*((4*H)^(2^C.gates.length))*((4*H)^(2^C.gates.length)))^(k+1))^k := by
  let T:=(4*H)^(2^C.gates.length)
  have hT : 1≤T := Nat.one_le_pow _ _ (by omega)
  apply clearedIntegerMatrix_det_eval_bound x _ (2*T*T) (by nlinarith)
  intro i j
  apply ((integerCircuitOutput C (o i)).derivative_evalHeight_bound x (v j)).trans
  have hh:=integerCircuitOutput_jetHeight_bound C hvalid x (v j) H hH hvar hconst (o i)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hh) hh

end APSCounting893.Main
end Component_39

section Component_40
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace APSCounting893.Main

lemma modulus_grid_exponential_gap (B : ℕ) : 4*(B+1)+1 < 2^(3*B+4) := by
  induction B with
  | zero => norm_num
  | succ B ih =>
    have he : 3*(B+1)+4=(3*B+4)+3 := by omega
    rw [he,pow_add]
    norm_num at *
    nlinarith

lemma exists_small_nondivisor (a B : ℕ) (ha : 0<a) (hB : a<2^B) :
    ∃ m : ℕ,2≤ m ∧ m≤4*(B+1) ∧ ¬m∣a := by
  by_contra hn
  push Not at hn
  let M:=4*(B+1)
  have hdiv : Nat.lcmUpto M ∣ a := by
    unfold Nat.lcmUpto
    apply Finset.lcm_dvd
    intro m hm
    have hmem:=Finset.mem_Icc.mp hm
    by_cases h1 : m=1
    · simp [h1]
    · exact hn m (by omega) hmem.2
  have hsmall : Nat.lcmUpto M < 2^B := (Nat.le_of_dvd ha hdiv).trans_lt hB
  have hlower:=Chebyshev.two_pow_le_mul_lcmUpto M
  have hupper : (M+1)*2^B<2^M := by
    have hh:=Nat.mul_lt_mul_of_pos_right (modulus_grid_exponential_gap B) (by positivity : 0<2^B)
    have he : (3*B+4)+B=M := by dsimp [M];omega
    simpa only [←pow_add,he] using hh
  have hh:=Nat.mul_lt_mul_of_pos_left hsmall (by omega : 0<M+1)
  omega

lemma exists_small_modulus_nonzero (z : ℤ) (B : ℕ) (hz : z≠0) (hB : z.natAbs<2^B) :
    ∃ m : ℕ,2≤ m ∧ m≤4*(B+1) ∧ (z : ZMod m)≠0 := by
  obtain ⟨m,hm,hM,hdiv⟩:=exists_small_nondivisor z.natAbs B (Int.natAbs_pos.mpr hz) hB
  refine ⟨m,hm,hM,?_⟩
  intro hzero
  have hd : (m : ℤ)∣z := (ZMod.intCast_zmod_eq_zero_iff_dvd z m).mp hzero
  exact hdiv (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd)

end APSCounting893.Main
end Component_40

section Component_41
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace APSCounting893.Main

lemma linear_circuit_jet_exponent_bound (L : ℕ) : 4*(L+1)+2≤2^(4*(L+1)) := by
  have hh:=modulus_grid_exponential_gap L
  have h1 : 4*(L+1)+2≤2^(3*L+4) := by omega
  exact h1.trans (Nat.pow_le_pow_right (by omega) (by omega))

lemma jacobian_minor_resource_degree (L k G : ℕ) (hk : k≤L) (hG : G≤L) :
    k*((k+1)*(2*2^G))≤2^(4*(L+1)) := by
  have hk1 : k≤2^L := hk.trans (Nat.lt_two_pow_self (n:=L)).le
  have hk2 : k+1≤2^(L+1) := (by omega : k+1≤L+1).trans (Nat.lt_two_pow_self (n:=L+1)).le
  have hg : 2*2^G≤2^(L+1) := by
    rw [pow_succ]
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) hG) |>.trans_eq (by ring)
  calc
    _ ≤ 2^L*(2^(L+1)*2^(L+1)) := Nat.mul_le_mul hk1 (Nat.mul_le_mul hk2 hg)
    _ = 2^(3*L+2) := by rw [←pow_add,←pow_add];congr 1;ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

lemma circuit_jet_resource_height (L G : ℕ) (hG : G≤L) :
    (4*2^(4*(L+1)))^(2^G)≤2^(2^(8*(L+1))) := by
  have hlin:=linear_circuit_jet_exponent_bound L
  have hE : (4*(L+1)+2)*2^G≤2^(8*(L+1)) := by
    calc
      _ ≤ 2^(4*(L+1))*2^L := Nat.mul_le_mul hlin (Nat.pow_le_pow_right (by omega) hG)
      _ = 2^(4*(L+1)+L) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hb : 4*2^(4*(L+1))=2^(4*(L+1)+2) := by rw [pow_add];norm_num;ring
  rw [hb,←pow_mul]
  exact Nat.pow_le_pow_right (by omega) hE

lemma doubled_square_resource_bound (u M : ℕ) (hu : 1≤u) (hM : M≤2^(2^(8*u))) :
    2*M*M≤2^(2^(16*u)) := by
  have hbase : 1≤2^(8*u) := Nat.one_le_pow _ _ (by omega)
  have hexp : 1+2*2^(8*u)≤2^(16*u) := by
    calc
      _ ≤ 4*2^(8*u) := by omega
      _ = 2^(8*u+2) := by rw [pow_add];norm_num;ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    _ ≤ 2*(2^(2^(8*u)))*(2^(2^(8*u))) := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) hM
    _ = 2^(1+2*2^(8*u)) := by
      have he : 1+2*2^(8*u)=(1+2^(8*u))+2^(8*u) := by omega
      rw [he,pow_add (2 : ℕ) (1+2^(8*u)) (2^(8*u)),pow_add (2 : ℕ) 1 (2^(8*u))]
      rfl
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hexp

lemma small_dimension_factorial_bound (L k : ℕ) (hk : k≤L) :
    k.factorial≤2^(2^(4*(L+1))) := by
  have hb : L+1≤2^(L+1) := (Nat.lt_two_pow_self (n:=L+1)).le
  have he : (L+1)*L≤2^(4*(L+1)) := by
    calc
      _ ≤ (L+1)*(L+1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 2^(L+1)*2^(L+1) := Nat.mul_le_mul hb hb
      _ = 2^(2*(L+1)) := by rw [←pow_add];congr 1;ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    _ ≤ k^k := Nat.factorial_le_pow k
    _ ≤ (L+1)^k := Nat.pow_le_pow_left (by omega) _
    _ ≤ (L+1)^L := Nat.pow_le_pow_right (by omega) hk
    _ ≤ (2^(L+1))^L := Nat.pow_le_pow_left hb _
    _ = 2^((L+1)*L) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) he

lemma small_dimension_product_bound (L k : ℕ) (hk : k≤L) : k*(k+1)≤2^(2*(L+1)) := by
  have hb : L+1≤2^(L+1) := (Nat.lt_two_pow_self (n:=L+1)).le
  calc
    _ ≤ (L+1)*(L+1) := Nat.mul_le_mul (by omega) (by omega)
    _ ≤ 2^(L+1)*2^(L+1) := Nat.mul_le_mul hb hb
    _ = _ := by rw [←pow_add];congr 1;ring

lemma cleared_minor_resource_height (L k M : ℕ) (hk : k≤L)
    (hM : M≤2^(2^(16*(L+1)))) :
    k.factorial*(M^(k+1))^k≤2^(2^(32*(L+1))) := by
  have hkprod:=small_dimension_product_bound L k hk
  have hpower : (M^(k+1))^k≤2^(2^(18*(L+1))) := by
    rw [←pow_mul]
    calc
      _ ≤ (2^(2^(16*(L+1))))^((k+1)*k) := Nat.pow_le_pow_left hM _
      _ = 2^(2^(16*(L+1))*((k+1)*k)) := (pow_mul _ _ _).symm
      _ ≤ 2^(2^(16*(L+1))*2^(2*(L+1))) :=
        Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (by simpa [Nat.mul_comm] using hkprod))
      _ = _ := by rw [←pow_add];congr 2;ring
  have hfac : k.factorial≤2^(2^(18*(L+1))) :=
    (small_dimension_factorial_bound L k hk).trans
      (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega)))
  calc
    _ ≤ 2^(2^(18*(L+1)))*2^(2^(18*(L+1))) := Nat.mul_le_mul hfac hpower
    _ = 2^(2^(18*(L+1)+1)) := by
      have he : 2^(18*(L+1))+2^(18*(L+1))=2^(18*(L+1)+1) := by rw [pow_succ];ring
      exact ((pow_add (2 : ℕ) (2^(18*(L+1))) (2^(18*(L+1)))).symm).trans (congrArg (fun e : ℕ => 2^e) he)
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))

end APSCounting893.Main
end Component_41

section Component_42
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace APSCounting893.Main

lemma modular_witness_grid_le_power (B : ℕ) : 4*(B*(8*(B+1))+1) ≤ 2^(8*(B+1)) := by
  have hb : B+1≤2^(B+1) := (Nat.lt_two_pow_self (n:=B+1)).le
  calc
    4*(B*(8*(B+1))+1) ≤ 64*(B+1)^2 := by nlinarith
    _ ≤ 64*(2^(B+1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _)
    _ = 2^(2*B+8) := by rw [←pow_mul,show (64 : ℕ)=2^6 from rfl,←pow_add];congr 1;ring
    _ ≤ 2^(8*(B+1)) := Nat.pow_le_pow_right (by omega) (by omega)

lemma dvd_power_of_prime_divisors {a m K : ℕ} (ha : a≠0) (hm : m≠0)
    (hsize : m≤2^K) (hdiv : ∀ p : ℕ,p.Prime → p∣m → p∣a) : m∣a^K := by
  apply (Nat.factorization_prime_le_iff_dvd hm (pow_ne_zero K ha)).mp
  intro p hp
  by_cases hpm : p∣m
  · have hpa:=hdiv p hp hpm
    have hapos : 1≤a.factorization p := hp.factorization_pos_of_dvd ha hpa
    have hmp : m.factorization p≤K :=
      Nat.factorization_le_of_le_pow (hsize.trans (Nat.pow_le_pow_left hp.two_le K))
    simp only [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul]
    nlinarith
  · simp only [Nat.factorization_eq_zero_of_not_dvd hpm]
    exact Nat.zero_le _

lemma exists_small_prime_not_dvd (a B : ℕ) (ha : 0<a) (hB : a<2^B) :
    ∃ p : ℕ,p.Prime ∧ p≤4*(B*(8*(B+1))+1) ∧ ¬p∣a := by
  let K:=8*(B+1)
  have hK : 0<K := by dsimp [K];omega
  have hpow : a^K<2^(B*K) := by
    simpa only [←pow_mul] using Nat.pow_lt_pow_left hB hK.ne'
  obtain ⟨m,hm,hM,hndiv⟩:=exists_small_nondivisor (a^K) (B*K) (pow_pos ha _) hpow
  by_contra hn
  push Not at hn
  apply hndiv
  apply dvd_power_of_prime_divisors ha.ne' (by omega)
  · exact hM.trans (modular_witness_grid_le_power B)
  · intro p hp hpm
    exact hn p hp ((Nat.le_of_dvd (by omega : 0< m) hpm).trans hM)

lemma exists_small_prime_modulus_nonzero (z : ℤ) (B : ℕ) (hz : z≠0) (hB : z.natAbs<2^B) :
    ∃ p : ℕ,p.Prime ∧ p≤4*(B*(8*(B+1))+1) ∧ (z : ZMod p)≠0 := by
  obtain ⟨p,hp,hM,hdiv⟩:=exists_small_prime_not_dvd z.natAbs B (Int.natAbs_pos.mpr hz) hB
  refine ⟨p,hp,hM,?_⟩
  intro hzero
  have hd : (p : ℤ)∣z := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hzero
  exact hdiv (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd)

end APSCounting893.Main
end Component_42

section Component_43
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace APSCounting893.Main

lemma prime_witness_bits_from_double_exponential_bound (L : ℕ) (z : ℤ) (hz : z≠0)
    (hsize : z.natAbs≤2^(2^(32*(L+1)))) :
    ∃ p : ℕ,p.Prime ∧ p.bits.length≤128*(L+1)+8 ∧ (z : ZMod p)≠0 := by
  let B:=2^(64*(L+1))
  have hbig : z.natAbs<2^B := by
    apply hsize.trans_lt
    apply Nat.pow_lt_pow_right (by decide : 1<2)
    exact Nat.pow_lt_pow_right (by decide : 1<2) (by omega)
  obtain ⟨p,hp,hpbound,hpz⟩:=exists_small_prime_modulus_nonzero z B hz hbig
  have hB : 1≤B := Nat.one_le_pow _ _ (by decide)
  have hM : 4*(B*(8*(B+1))+1)≤128*B^2 := by nlinarith
  have hpow : 128*B^2=2^(128*(L+1)+7) := by
    dsimp only [B]
    rw [show (128 : ℕ)=2^7 from rfl,←pow_mul,←pow_add]
    congr 1
    ring
  have hle : p≤2^(128*(L+1)+7) := (hpbound.trans hM).trans_eq hpow
  refine ⟨p,hp,?_,hpz⟩
  rw [Nat.size_eq_bits_len]
  simpa only [Nat.size_pow] using Nat.size_le_size hle

end APSCounting893.Main
end Component_43

section Component_44

set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial Finset Fintype
namespace APSCounting893.Main

open Classical in
lemma finite_grid_success_lower_bound {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (hp : p ≠ 0) (B : Finset R) (hB : B.Nonempty)
    (D : ℕ) (hD : p.totalDegree ≤ D) (Good : (Fin n → R) → Prop)
    (hgood : ∀ x ∈ piFinset (fun _ : Fin n => B), MvPolynomial.eval x p ≠ 0 → Good x) :
    ((piFinset (fun _ : Fin n => B)).filter Good).card / (B.card ^ n : ℝ) ≥
      1 - (D : ℝ) / B.card := by
  classical
  have hs := MvPolynomial.schwartz_zippel_totalDegree hp B
  have hsR : (((piFinset (fun _ : Fin n => B)).filter (fun x => MvPolynomial.eval x p = 0)).card : ℝ) /
      (B.card ^ n : ℝ) ≤ (p.totalDegree : ℝ) / B.card := by
    have hh := (NNRat.cast_le (K := ℝ)).mpr hs
    simpa only [NNRat.cast_div,NNRat.cast_pow,NNRat.cast_natCast] using hh
  have hcard : (piFinset (fun _ : Fin n => B)).card = B.card ^ n := by simp
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := piFinset (fun _ : Fin n => B)) (p := fun x => MvPolynomial.eval x p = 0)
  have hle : ((piFinset (fun _ : Fin n => B)).filter (fun x => MvPolynomial.eval x p ≠ 0)).card ≤
      ((piFinset (fun _ : Fin n => B)).filter Good).card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hx,hne⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx,hgood x hx hne⟩
  have hden : (0 : ℝ) < B.card ^ n := by positivity
  have hb : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hsplitR :
      (((piFinset (fun _ : Fin n => B)).filter (fun x => MvPolynomial.eval x p = 0)).card : ℝ) +
      (((piFinset (fun _ : Fin n => B)).filter (fun x => MvPolynomial.eval x p ≠ 0)).card : ℝ) =
        (B.card ^ n : ℝ) := by exact_mod_cast (hsplit.trans hcard)
  have hleR :
      (((piFinset (fun _ : Fin n => B)).filter (fun x => MvPolynomial.eval x p ≠ 0)).card : ℝ) ≤
      (((piFinset (fun _ : Fin n => B)).filter Good).card : ℝ) := by exact_mod_cast hle
  have hdeg : (p.totalDegree : ℝ) / B.card ≤ (D : ℝ) / B.card := by gcongr
  have hbound := hsR.trans hdeg
  apply (le_div_iff₀ hden).mpr
  have hh := (div_le_iff₀ hden).mp hbound
  have htmp : (1-(D : ℝ)/B.card)*(B.card^n : ℝ) =
      (B.card^n : ℝ) - ((D : ℝ)/B.card)*(B.card^n : ℝ) := by ring
  rw [htmp]
  linarith

end APSCounting893.Main
end Component_44

section Component_45
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma exists_integer_grid_eval_ne_zero {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (hp : p≠0) :
    ∃ x : Fin n → ℤ,(∀ i,0≤x i ∧ x i≤(p.totalDegree : ℤ)) ∧ MvPolynomial.eval x p≠0 := by
  classical
  let D:=p.totalDegree
  let B : Finset ℤ:=(Finset.range (D+1)).image Int.ofNat
  have hB : B.Nonempty := by exact ⟨0,Finset.mem_image.mpr ⟨0,by simp,by simp⟩⟩
  have hcard : B.card=D+1 := by simp [B,Finset.card_image_of_injective,Int.ofNat_injective]
  have hs:=finite_grid_success_lower_bound p hp B hB D le_rfl (fun x => MvPolynomial.eval x p≠0)
    (fun x hx hpx => hpx)
  have hpos : 0<1-(D : ℝ)/(D+1) := by
    have hd : (0 : ℝ)<D+1 := by positivity
    have hl : (D : ℝ)/(D+1)<1 := (div_lt_one hd).mpr (by linarith)
    linarith
  have hcardpos : 0<((Fintype.piFinset (fun _ : Fin n => B)).filter (fun x => MvPolynomial.eval x p≠0)).card := by
    by_contra hz
    have he : ((Fintype.piFinset (fun _ : Fin n => B)).filter (fun x => MvPolynomial.eval x p≠0)).card=0 := by omega
    have hh : (0 : ℝ) ≥ 1-(D : ℝ)/(D+1) := by simpa [he,hcard] using hs
    exact (not_le_of_gt hpos) hh
  obtain ⟨x,hx⟩:=Finset.card_pos.mp hcardpos
  obtain ⟨hx,hpx⟩:=Finset.mem_filter.mp hx
  refine ⟨x,?_,hpx⟩
  intro i
  have hi:=Fintype.mem_piFinset.mp hx i
  obtain ⟨a,ha,hea⟩:=Finset.mem_image.mp hi
  rw [←hea]
  have hlt:=Finset.mem_range.mp ha
  exact ⟨Int.natCast_nonneg a,by
    change (a : ℤ)≤(D : ℤ)
    exact_mod_cast (by omega : a≤D)⟩

end APSCounting893.Main
end Component_45

section Component_46
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace APSCounting893.Main

lemma encodeNat_length_pos (n : ℕ) : 0<(encodeNat n).length := by
  simp [encodeNat]

lemma arithmeticGate_encode_length_pos {n : ℕ} (g : ArithmeticGate n) : 0<g.encode.length := by
  cases g <;> simp [ArithmeticGate.encode,encodeNat]

lemma gates_length_le_flatMap_encode {n : ℕ} (gs : List (ArithmeticGate n)) :
    gs.length≤(gs.flatMap ArithmeticGate.encode).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg:=arithmeticGate_encode_length_pos g
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

lemma circuit_gates_length_le_encode {n : ℕ} (C : ArithmeticCircuit n) : C.gates.length≤C.encode.length := by
  have hh:=gates_length_le_flatMap_encode C.gates
  simp only [ArithmeticCircuit.encode,encodeList,List.length_append]
  omega

lemma output_count_le_encode {n : ℕ} (C : ArithmeticCircuit n) : C.outputs.length≤C.encode.length := by
  have hh : C.outputs.length≤(C.outputs.flatMap encodeNat).length := by
    induction C.outputs with
    | nil => rfl
    | cons o os ih =>
      have ho:=encodeNat_length_pos o
      simp only [List.length_cons,List.flatMap_cons,List.length_append]
      omega
  simp only [ArithmeticCircuit.encode,encodeList,List.length_append]
  omega

lemma ReducedCircuit.dimension_le_encode (I : ReducedCircuit) : I.n+1≤I.C.encode.length := by
  rw [←I.outputCount]
  exact output_count_le_encode I.C

end APSCounting893.Main
end Component_46

section Component_47
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma member_flatMap_length_le {α β : Type} (xs : List α) (f : α → List β) (x : α) (hx : x∈xs) :
    (f x).length≤(xs.flatMap f).length := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with h|h
    · subst a
      simp only [List.flatMap_cons,List.length_append]
      omega
    · have hh:=ih h
      simp only [List.flatMap_cons,List.length_append]
      omega

lemma encodeNat_bits_length_le (a : ℕ) : a.bits.length≤(encodeNat a).length := by simp [encodeNat]

lemma encodeRat_num_bits_length_le (q : ℚ) : q.num.natAbs.bits.length≤(encodeRat q).length := by
  simp [encodeRat,encodeInt,encodeNat]
  omega

lemma encodeRat_den_bits_length_le (q : ℚ) : q.den.bits.length≤(encodeRat q).length := by
  simp [encodeRat,encodeInt,encodeNat]
  omega

lemma constant_head_bits_length_le {n : ℕ} (cs : List ℚ) :
    (cs.headD 0).num.natAbs.bits.length≤(ArithmeticGate.constant (n:=n) cs).encode.length ∧
      (cs.headD 0).den.bits.length≤(ArithmeticGate.constant (n:=n) cs).encode.length := by
  cases cs with
  | nil => simp [ArithmeticGate.encode,encodeList,encodeNat,encodeRat,encodeInt]
  | cons q qs =>
    have hh:=member_flatMap_length_le (q::qs) encodeRat q (by simp)
    have hn:=encodeRat_num_bits_length_le q
    have hd:=encodeRat_den_bits_length_le q
    simp only [List.headD_cons,ArithmeticGate.encode,encodeList,List.length_append]
    exact ⟨by omega,by omega⟩

lemma circuit_gate_encoding_length_le {n : ℕ} (C : ArithmeticCircuit n) (g : ArithmeticGate n) (hg : g∈C.gates) :
    g.encode.length≤C.encode.length := by
  have hh:=member_flatMap_length_le C.gates ArithmeticGate.encode g hg
  simp only [ArithmeticCircuit.encode,encodeList,List.length_append]
  omega

lemma circuit_constant_head_bound {n : ℕ} (C : ArithmeticCircuit n) (cs : List ℚ)
    (hcs : ArithmeticGate.constant cs∈C.gates) :
    (cs.headD 0).num.natAbs<2^C.encode.length ∧ (cs.headD 0).den<2^C.encode.length := by
  have hg:=circuit_gate_encoding_length_le C (.constant cs) hcs
  have hh:=constant_head_bits_length_le (n:=n) cs
  constructor
  · apply Nat.size_le.mp
    rw [←Nat.size_eq_bits_len]
    exact hh.1.trans hg
  · apply Nat.size_le.mp
    rw [←Nat.size_eq_bits_len]
    exact hh.2.trans hg

end APSCounting893.Main
end Component_47

section Component_48
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma circuitJacobianIntegerMinor_ne_zero_iff_modular {n k : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n)
    (ho : Function.Injective o) :
    circuitJacobianIntegerMinor C o v≠0 ↔
      ∃ p : ℕ,p.Prime ∧ p.bits.length≤128*(C.encode.length+1)+8 ∧
        ∃ x : Fin n → ℤ,(∀ i,0≤x i ∧ x i≤(2^(4*(C.encode.length+1)) : ℕ)) ∧
          (MvPolynomial.eval x (circuitJacobianIntegerMinor C o v) : ZMod p)≠0 := by
  constructor
  · intro hne
    let L:=C.encode.length
    let H:=2^(4*(L+1))
    have hko : k≤C.outputs.length := by simpa using Fintype.card_le_of_injective o ho
    have hk : k≤L := hko.trans (output_count_le_encode C)
    have hG:=circuit_gates_length_le_encode C
    have hdegree : (circuitJacobianIntegerMinor C o v).totalDegree≤H :=
      (circuitJacobianIntegerMinor_degree_bound C hvalid o v).trans
        (jacobian_minor_resource_degree L k C.gates.length hk hG)
    obtain ⟨x,hx,hpx⟩:=exists_integer_grid_eval_ne_zero _ hne
    have hxH : ∀ i,0≤x i ∧ x i≤(H : ℤ) := by
      intro i
      exact ⟨(hx i).1,(hx i).2.trans (by exact_mod_cast hdegree)⟩
    have hvar : ∀ i,(x i).natAbs≤H := by
      intro i
      have hh:=(hxH i).2
      rw [←Int.natAbs_of_nonneg (hxH i).1] at hh
      exact_mod_cast hh
    have hH : 1≤H := Nat.one_le_pow _ _ (by decide)
    have hconst : ∀ g ∈ C.gates,match g with
        | .constant cs => (cs.headD 0).num.natAbs≤H ∧ (cs.headD 0).den≤H
        | _ => True := by
      intro g hg
      cases g with
      | «constant» cs =>
        have hh:=circuit_constant_head_bound C cs hg
        have hL : 2^L≤H := Nat.pow_le_pow_right (by decide) (by dsimp [L,H];omega)
        exact ⟨hh.1.le.trans hL,hh.2.le.trans hL⟩
      | «variable» i | add a b | sub a b | mul a b | div a b => trivial
    let T:=(4*H)^(2^C.gates.length)
    let M:=2*T*T
    have hT : T≤2^(2^(8*(L+1))) := circuit_jet_resource_height L C.gates.length hG
    have hM : M≤2^(2^(16*(L+1))) := doubled_square_resource_bound (L+1) T (by omega) hT
    have hvalue : (MvPolynomial.eval x (circuitJacobianIntegerMinor C o v)).natAbs≤2^(2^(32*(L+1))) :=
      (circuitJacobianIntegerMinor_eval_bound C hvalid o v x H hH hvar hconst).trans
        (cleared_minor_resource_height L k M hk hM)
    obtain ⟨p,hp,hplen,hpz⟩:=prime_witness_bits_from_double_exponential_bound L _ hpx hvalue
    exact ⟨p,hp,hplen,x,hxH,hpz⟩
  · rintro ⟨p,hp,hplen,x,hx,hpx⟩ hz
    apply hpx
    simp only [hz,map_zero,Int.cast_zero]

end APSCounting893.Main
end Component_48

section Component_49
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def circuitActiveVariables {n : ℕ} (C : ArithmeticCircuit n) : Finset (Fin n) :=
  (C.gates.filterMap fun g => match g with | .variable i => some i | _ => none).toFinset

lemma circuitActiveVariables_mem_iff {n : ℕ} (C : ArithmeticCircuit n) (i : Fin n) :
    i∈circuitActiveVariables C ↔ ArithmeticGate.variable i∈C.gates := by
  classical
  simp only [circuitActiveVariables,List.mem_toFinset,List.mem_filterMap]
  constructor
  · rintro ⟨g,hg,hi⟩
    cases g <;> simp_all
  · intro hi
    exact ⟨.variable i,hi,rfl⟩

lemma circuitActiveVariables_card_le {n : ℕ} (C : ArithmeticCircuit n) :
    (circuitActiveVariables C).card≤C.gates.length := by
  exact (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

lemma active_variable_index_bits_le {n : ℕ} (C : ArithmeticCircuit n) (i : Fin n)
    (hi : i∈circuitActiveVariables C) : i.val.bits.length≤C.encode.length := by
  have hg:=circuit_gate_encoding_length_le C (.variable i) ((circuitActiveVariables_mem_iff C i).mp hi)
  have hh : i.val.bits.length≤(ArithmeticGate.variable i).encode.length := by
    simp only [ArithmeticGate.encode,List.length_append]
    exact (encodeNat_bits_length_le _).trans (by omega)
  exact hh.trans hg

end APSCounting893.Main
end Component_49

section Component_50
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace APSCounting893.Main

noncomputable def restrictCircuitAssignment {n : ℕ} (C : ArithmeticCircuit n) (x : Fin n → ℤ) :
    List (Fin n × ℤ) := (circuitActiveVariables C).toList.map (fun i => (i,x i))

lemma restrictCircuitAssignment_length {n : ℕ} (C : ArithmeticCircuit n) (x : Fin n → ℤ) :
    (restrictCircuitAssignment C x).length≤C.encode.length := by
  simpa only [restrictCircuitAssignment,List.length_map,Finset.length_toList] using
    (circuitActiveVariables_card_le C).trans (circuit_gates_length_le_encode C)

lemma restrictCircuitAssignment_mem {n : ℕ} (C : ArithmeticCircuit n) (x : Fin n → ℤ)
    (p : Fin n × ℤ) (hp : p∈restrictCircuitAssignment C x) :
    p.1∈circuitActiveVariables C ∧ p.2=x p.1 := by
  obtain ⟨i,hi,he⟩:=List.mem_map.mp hp
  subst p
  exact ⟨Finset.mem_toList.mp hi,rfl⟩

lemma restrictCircuitAssignment_agrees {n : ℕ} (C : ArithmeticCircuit n) (x : Fin n → ℤ)
    (i : Fin n) (hi : i∈circuitActiveVariables C) :
    sparseAssignmentPoint (restrictCircuitAssignment C x) i=x i := by
  unfold sparseAssignmentPoint restrictCircuitAssignment
  rw [List.lookup_graph x (Finset.mem_toList.mpr hi)]
  rfl

end APSCounting893.Main
end Component_50

section Component_51
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma polynomial_vars_add_in {σ K : Type} [CommRing K] [DecidableEq σ] (S : Finset σ)
    (p q : MvPolynomial σ K) (hp : p.vars⊆S) (hq : q.vars⊆S) : (p+q).vars⊆S :=
  (MvPolynomial.vars_add_subset _ _).trans (Finset.union_subset hp hq)
lemma polynomial_vars_sub_in {σ K : Type} [CommRing K] [DecidableEq σ] (S : Finset σ)
    (p q : MvPolynomial σ K) (hp : p.vars⊆S) (hq : q.vars⊆S) : (p-q).vars⊆S :=
  (MvPolynomial.vars_sub_subset (p:=p) (q:=q)).trans (Finset.union_subset hp hq)
lemma polynomial_vars_mul_in {σ K : Type} [CommRing K] [DecidableEq σ] (S : Finset σ)
    (p q : MvPolynomial σ K) (hp : p.vars⊆S) (hq : q.vars⊆S) : (p*q).vars⊆S :=
  (MvPolynomial.vars_mul _ _).trans (Finset.union_subset hp hq)

lemma IntegerPolynomialPair.add_vars_in {n : ℕ} (S : Finset (Fin n)) (p q : IntegerPolynomialPair n)
    (hp : p.1.vars⊆S ∧ p.2.vars⊆S) (hq : q.1.vars⊆S ∧ q.2.vars⊆S) :
    (p.add q).1.vars⊆S ∧ (p.add q).2.vars⊆S := by
  change (p.1*q.2+q.1*p.2).vars⊆S ∧ (p.2*q.2).vars⊆S
  exact ⟨polynomial_vars_add_in S _ _ (polynomial_vars_mul_in S _ _ hp.1 hq.2) (polynomial_vars_mul_in S _ _ hq.1 hp.2),polynomial_vars_mul_in S _ _ hp.2 hq.2⟩

lemma IntegerPolynomialPair.sub_vars_in {n : ℕ} (S : Finset (Fin n)) (p q : IntegerPolynomialPair n)
    (hp : p.1.vars⊆S ∧ p.2.vars⊆S) (hq : q.1.vars⊆S ∧ q.2.vars⊆S) :
    (p.sub q).1.vars⊆S ∧ (p.sub q).2.vars⊆S := by
  change (p.1*q.2-q.1*p.2).vars⊆S ∧ (p.2*q.2).vars⊆S
  exact ⟨polynomial_vars_sub_in S _ _ (polynomial_vars_mul_in S _ _ hp.1 hq.2) (polynomial_vars_mul_in S _ _ hq.1 hp.2),polynomial_vars_mul_in S _ _ hp.2 hq.2⟩

lemma IntegerPolynomialPair.mul_vars_in {n : ℕ} (S : Finset (Fin n)) (p q : IntegerPolynomialPair n)
    (hp : p.1.vars⊆S ∧ p.2.vars⊆S) (hq : q.1.vars⊆S ∧ q.2.vars⊆S) :
    (p.mul q).1.vars⊆S ∧ (p.mul q).2.vars⊆S := by
  change (p.1*q.1).vars⊆S ∧ (p.2*q.2).vars⊆S
  exact ⟨polynomial_vars_mul_in S _ _ hp.1 hq.1,polynomial_vars_mul_in S _ _ hp.2 hq.2⟩

lemma IntegerPolynomialPair.div_vars_in {n : ℕ} (S : Finset (Fin n)) (p q : IntegerPolynomialPair n)
    (hp : p.1.vars⊆S ∧ p.2.vars⊆S) (hq : q.1.vars⊆S ∧ q.2.vars⊆S) :
    (p.div q).1.vars⊆S ∧ (p.div q).2.vars⊆S := by
  change (p.1*q.2).vars⊆S ∧ (p.2*q.1).vars⊆S
  exact ⟨polynomial_vars_mul_in S _ _ hp.1 hq.2,polynomial_vars_mul_in S _ _ hp.2 hq.1⟩

lemma integerGateValue_vars_in {n : ℕ} (S : Finset (Fin n)) (prior : List (IntegerPolynomialPair n))
    (hprior : ∀ p ∈ prior,p.1.vars⊆S ∧ p.2.vars⊆S) (g : ArithmeticGate n)
    (hg : match g with | .variable i => i∈S | _ => True)
    (p : IntegerPolynomialPair n) (hp : integerGateValue prior g=some p) : p.1.vars⊆S ∧ p.2.vars⊆S := by
  cases g with
  | «variable» i =>
    simp only [integerGateValue,Option.some.injEq] at hp
    subst p
    simpa only [MvPolynomial.vars_X,MvPolynomial.vars_one,Finset.singleton_subset_iff,
      Finset.empty_subset,and_true] using hg
  | «constant» cs =>
    simp only [integerGateValue,Option.some.injEq] at hp
    subst p
    simp only [MvPolynomial.vars_C,Finset.empty_subset,and_self]
  | add a b | sub a b | mul a b | div a b =>
    cases ha : prior[a]? <;> cases hb : prior[b]? <;> simp [integerGateValue,ha,hb] at hp
    subst p
    rename_i p q
    obtain ⟨hp1,hp2⟩:=hprior p (List.mem_of_getElem? ha)
    obtain ⟨hq1,hq2⟩:=hprior q (List.mem_of_getElem? hb)
    first
    | exact IntegerPolynomialPair.add_vars_in S p q ⟨hp1,hp2⟩ ⟨hq1,hq2⟩
    | exact IntegerPolynomialPair.sub_vars_in S p q ⟨hp1,hp2⟩ ⟨hq1,hq2⟩
    | exact IntegerPolynomialPair.mul_vars_in S p q ⟨hp1,hp2⟩ ⟨hq1,hq2⟩
    | exact IntegerPolynomialPair.div_vars_in S p q ⟨hp1,hp2⟩ ⟨hq1,hq2⟩

end APSCounting893.Main
end Component_51

section Component_52
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma integerCircuitValues_vars_in {n : ℕ} (C : ArithmeticCircuit n)
    (ps : List (IntegerPolynomialPair n)) (hps : integerCircuitValues C=some ps) :
    ∀ p ∈ ps,p.1.vars⊆circuitActiveVariables C ∧ p.2.vars⊆circuitActiveVariables C := by
  let S:=circuitActiveVariables C
  let step := fun (acc : Option (List (IntegerPolynomialPair n))) (g : ArithmeticGate n) => do
    let prior ← acc
    let p ← integerGateValue prior g
    return prior++[p]
  have hnone (gs : List (ArithmeticGate n)) : gs.foldl step none=none := by
    induction gs with
    | nil => rfl
    | cons g gs ih => exact ih
  have hfold (gs : List (ArithmeticGate n))
      (hgs : ∀ g ∈ gs,match g with | .variable i => i∈S | _ => True)
      (prior : List (IntegerPolynomialPair n)) (hprior : ∀ p ∈ prior,p.1.vars⊆S ∧ p.2.vars⊆S)
      (out : List (IntegerPolynomialPair n)) (hout : gs.foldl step (some prior)=some out) :
      ∀ p ∈ out,p.1.vars⊆S ∧ p.2.vars⊆S := by
    induction gs generalizing prior out with
    | nil =>
      have he : prior=out := Option.some.inj hout
      subst out
      exact hprior
    | cons g gs ih =>
      rw [List.foldl_cons] at hout
      change gs.foldl step ((integerGateValue prior g).bind (fun p => some (prior++[p])))=some out at hout
      cases hg : integerGateValue prior g with
      | none => simp only [hg,Option.bind_none,hnone] at hout;cases hout
      | some q =>
        have hq:=integerGateValue_vars_in S prior hprior g (hgs g (by simp)) q hg
        have hnew : ∀ p ∈ prior++[q],p.1.vars⊆S ∧ p.2.vars⊆S := by
          intro p hp
          rcases List.mem_append.mp hp with hp|hp
          · exact hprior p hp
          · have he : p=q := by simpa using hp
            simpa only [he] using hq
        have hh : gs.foldl step (some (prior++[q]))=some out := by simpa only [hg,Option.bind_some] using hout
        exact ih (fun g hg => hgs g (by simp [hg])) (prior++[q]) hnew out hh
  apply hfold C.gates ?_ [] (by simp) ps hps
  intro g hg
  cases g with
  | «variable» i => exact (circuitActiveVariables_mem_iff C i).mpr hg
  | «constant» cs | add a b | sub a b | mul a b | div a b => trivial

lemma integerCircuitOutput_vars_in {n : ℕ} (C : ArithmeticCircuit n) (hvalid : ValidCircuit .rational C)
    (j : Fin C.outputs.length) :
    (integerCircuitOutput C j).1.vars⊆circuitActiveVariables C ∧
      (integerCircuitOutput C j).2.vars⊆circuitActiveVariables C := by
  obtain ⟨values,hv,hout⟩:=hvalid.2
  obtain ⟨ps,hps,hden,hmap⟩:=integerCircuitValues_of_success C values hv
  exact integerCircuitValues_vars_in C ps hps _ (integerCircuitOutput_mem_values C hvalid ps hps j)

end APSCounting893.Main
end Component_52

section Component_53
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace APSCounting893.Main

lemma polynomial_pderiv_vars_subset {K σ : Type} [CommSemiring K] [DecidableEq σ]
    (p : MvPolynomial σ K) (j : σ) : (MvPolynomial.pderiv j p).vars⊆p.vars := by
  classical
  intro i hi
  obtain ⟨m,hm,him⟩:=(MvPolynomial.mem_vars_iff_mem_support i).mp hi
  have hc:=MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hc
  have hp : p.coeff (m+Finsupp.single j 1)≠0 := by
    intro hz
    simp only [hz,zero_mul] at hc
    exact hc rfl
  apply (MvPolynomial.mem_vars_iff_mem_support i).mpr
  refine ⟨m+Finsupp.single j 1,MvPolynomial.mem_support_iff.mpr hp,?_⟩
  rw [Finsupp.mem_support_iff] at him ⊢
  simp only [Finsupp.add_apply]
  omega

end APSCounting893.Main
end Component_53

section Component_54
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace APSCounting893.Main

lemma polynomial_vars_prod_in {σ K ι : Type} [CommRing K] [DecidableEq σ]
    (S : Finset σ) (s : Finset ι) (f : ι → MvPolynomial σ K) (hf : ∀ i ∈ s,(f i).vars⊆S) :
    (∏ i ∈ s,f i).vars⊆S := by
  classical
  apply (MvPolynomial.vars_prod f).trans
  intro i hi
  obtain ⟨a,ha,hia⟩:=Finset.mem_biUnion.mp hi
  exact hf a ha hia

lemma polynomial_vars_sum_in {σ K ι : Type} [CommRing K] [DecidableEq σ]
    (S : Finset σ) (s : Finset ι) (f : ι → MvPolynomial σ K) (hf : ∀ i ∈ s,(f i).vars⊆S) :
    (∑ i ∈ s,f i).vars⊆S := by
  classical
  apply (MvPolynomial.vars_sum_subset s f).trans
  intro i hi
  obtain ⟨a,ha,hia⟩:=Finset.mem_biUnion.mp hi
  exact hf a ha hia

lemma polynomial_matrix_det_vars_in {σ : Type} [DecidableEq σ] {r : ℕ}
    (S : Finset σ) (A : Matrix (Fin r) (Fin r) (MvPolynomial σ ℤ))
    (hA : ∀ i j,(A i j).vars⊆S) : A.det.vars⊆S := by
  classical
  rw [Matrix.det_apply]
  apply polynomial_vars_sum_in
  intro e he
  change (((Equiv.Perm.sign e : ℤ) • ∏ i,A (e i) i)).vars⊆S
  rw [MvPolynomial.smul_eq_C_mul]
  apply polynomial_vars_mul_in
  · simp only [MvPolynomial.vars_C,Finset.empty_subset]
  · exact polynomial_vars_prod_in S _ _ (fun i hi => hA _ _)

end APSCounting893.Main
end Component_54

section Component_55
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma IntegerPolynomialPair.derivative_vars_in {n : ℕ} (S : Finset (Fin n)) (j : Fin n)
    (p : IntegerPolynomialPair n) (hp : p.1.vars⊆S ∧ p.2.vars⊆S) :
    (p.derivative j).1.vars⊆S ∧ (p.derivative j).2.vars⊆S := by
  constructor
  · change (MvPolynomial.pderiv j p.1*p.2-p.1*MvPolynomial.pderiv j p.2).vars⊆S
    exact polynomial_vars_sub_in S _ _
      (polynomial_vars_mul_in S _ _ ((polynomial_pderiv_vars_subset _ _).trans hp.1) hp.2)
      (polynomial_vars_mul_in S _ _ hp.1 ((polynomial_pderiv_vars_subset _ _).trans hp.2))
  · exact (MvPolynomial.vars_pow p.2 2).trans hp.2

lemma circuitJacobianIntegerMinor_vars_in {n k : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) :
    (circuitJacobianIntegerMinor C o v).vars⊆circuitActiveVariables C := by
  apply polynomial_matrix_det_vars_in
  intro i j
  have hA (i j : Fin k) : (circuitJacobianIntegerPairs C o v i j).1.vars⊆circuitActiveVariables C ∧
      (circuitJacobianIntegerPairs C o v i j).2.vars⊆circuitActiveVariables C :=
    IntegerPolynomialPair.derivative_vars_in _ _ _ (integerCircuitOutput_vars_in C hvalid (o i))
  apply polynomial_vars_mul_in
  · exact (hA i j).1
  · apply polynomial_vars_prod_in
    intro a ha
    exact (hA i a).2

lemma circuitJacobianIntegerMinor_active_indices {n k : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n)
    (hne : circuitJacobianIntegerMinor C o v≠0) (j : Fin k) : v j∈circuitActiveVariables C := by
  by_contra hj
  have hdet:=(circuitJacobianIntegerMinor_ne_zero_iff C hvalid o v).mp hne
  apply hdet
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro i
  have hvars:=integerCircuitOutput_vars_in C hvalid (o i)
  have hN : MvPolynomial.pderiv (v j) (integerCircuitOutput C (o i)).1=0 :=
    MvPolynomial.pderiv_eq_zero_of_notMem_vars (fun hi => hj (hvars.1 hi))
  have hD : MvPolynomial.pderiv (v j) (integerCircuitOutput C (o i)).2=0 :=
    MvPolynomial.pderiv_eq_zero_of_notMem_vars (fun hi => hj (hvars.2 hi))
  have hpair : (circuitJacobianIntegerPairs C o v i j).value=0 := by
    simp only [circuitJacobianIntegerPairs,IntegerPolynomialPair.derivative,IntegerPolynomialPair.value,
      hN,hD,zero_mul,mul_zero,sub_self,map_zero,zero_div]
  have hh:=(circuitJacobianIntegerPairs_value C hvalid o v i j).symm.trans hpair
  apply IsFractionRing.injective (MvPolynomial (Fin n) CoefficientPresentation.rational.Field)
    (CircuitFunctionField .rational n)
  exact hh.trans (map_zero _).symm

end APSCounting893.Main
end Component_55

section Component_56
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma polynomial_eval_eq_of_vars_agree {σ K : Type} [CommRing K] [DecidableEq σ]
    (p : MvPolynomial σ K) (x y : σ → K) (h : ∀ i ∈ p.vars,x i=y i) :
    MvPolynomial.eval x p=MvPolynomial.eval y p := by
  apply MvPolynomial.eval₂Hom_congr' rfl ?_ rfl
  intro i hi hi'
  exact h i hi

lemma circuitJacobianIntegerMinor_sparse_eval {n k : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n)
    (x : Fin n → ℤ) :
    MvPolynomial.eval (sparseAssignmentPoint (restrictCircuitAssignment C x)) (circuitJacobianIntegerMinor C o v)=
      MvPolynomial.eval x (circuitJacobianIntegerMinor C o v) := by
  apply polynomial_eval_eq_of_vars_agree
  intro i hi
  exact restrictCircuitAssignment_agrees C x i (circuitJacobianIntegerMinor_vars_in C hvalid o v hi)

end APSCounting893.Main
end Component_56

section Component_57
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace APSCounting893.Main

lemma encodeNat_length_formula (a : ℕ) : (encodeNat a).length=2*a.bits.length+1 := by
  simp [encodeNat]
  omega

lemma flatMap_length_bound {α β : Type} (xs : List α) (f : α → List β) (M : ℕ)
    (h : ∀ x ∈ xs,(f x).length≤M) : (xs.flatMap f).length≤xs.length*M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx:=h x (by simp)
    have ht:=ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith

lemma sparseAssignment_encoding_length_bound {n : ℕ} (a : List (Fin n × ℤ)) (L : ℕ)
    (hlen : a.length≤L)
    (hkeys : ∀ p ∈ a,p.1.val.bits.length≤L)
    (hvalues : ∀ p ∈ a,p.2.natAbs.bits.length≤4*(L+1)+1) :
    (encodeSparseAssignment a).length≤polyBound 32 2 L := by
  have heach : ∀ p ∈ a,(encodeNat p.1.val++encodeInt p.2).length≤10*L+13 := by
    intro p hp
    have hk:=hkeys p hp
    have hv:=hvalues p hp
    simp only [encodeInt,List.length_append,List.length_cons,List.length_nil,encodeNat_length_formula]
    omega
  have hflat:=flatMap_length_bound a (fun p => encodeNat p.1.val++encodeInt p.2) (10*L+13) heach
  have hbits : a.length.bits.length≤L := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=a.length))).trans hlen
  unfold encodeSparseAssignment encodeList polyBound
  simp only [List.length_append,encodeNat_length_formula]
  nlinarith [Nat.mul_le_mul_right (10*L+13) hlen]

end APSCounting893.Main
end Component_57

section Component_58
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma circuitJacobianIntegerMinor_ne_zero_iff_sparse_modular {n k : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n)
    (ho : Function.Injective o) :
    circuitJacobianIntegerMinor C o v≠0 ↔
      ∃ p : ℕ,p.Prime ∧ p.bits.length≤128*(C.encode.length+1)+8 ∧
        ∃ a : List (Fin n × ℤ),(encodeSparseAssignment a).length≤polyBound 32 2 C.encode.length ∧
          (MvPolynomial.eval (sparseAssignmentPoint a) (circuitJacobianIntegerMinor C o v) : ZMod p)≠0 := by
  constructor
  · intro hne
    obtain ⟨p,hp,hplen,x,hx,hpx⟩:=(circuitJacobianIntegerMinor_ne_zero_iff_modular C hvalid o v ho).mp hne
    let a:=restrictCircuitAssignment C x
    have hlen : a.length≤C.encode.length := restrictCircuitAssignment_length C x
    have hkeys : ∀ z ∈ a,z.1.val.bits.length≤C.encode.length := by
      intro z hz
      have ha:=restrictCircuitAssignment_mem C x z hz
      exact active_variable_index_bits_le C z.1 ha.1
    have hvalues : ∀ z ∈ a,z.2.natAbs.bits.length≤4*(C.encode.length+1)+1 := by
      intro z hz
      have ha:=restrictCircuitAssignment_mem C x z hz
      rw [ha.2,Nat.size_eq_bits_len]
      have hn : (x z.1).natAbs≤2^(4*(C.encode.length+1)) := by
        have hh:=(hx z.1).2
        rw [←Int.natAbs_of_nonneg (hx z.1).1] at hh
        exact_mod_cast hh
      simpa only [Nat.size_pow] using Nat.size_le_size hn
    refine ⟨p,hp,hplen,a,sparseAssignment_encoding_length_bound a _ hlen hkeys hvalues,?_⟩
    simpa only [a,circuitJacobianIntegerMinor_sparse_eval C hvalid o v x] using hpx
  · rintro ⟨p,hp,hplen,a,halen,hpx⟩ hz
    apply hpx
    simp only [hz,map_zero,Int.cast_zero]

end APSCounting893.Main
end Component_58

section Component_59
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma bounded_modular_dimension_certificates_proof {n : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) :
    ∃ r : ℕ,RSCapacity.algDim (imageClosure (rationalComplexPolynomials C))=((r : ℕ∞) : WithBot ℕ∞) ∧
      ∀ k : ℕ,k≤r ↔ ∃ (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n),
        Function.Injective o ∧ Function.Injective v ∧
        (∀ j,(v j).val.bits.length≤C.encode.length) ∧
        ∃ p : ℕ,p.Prime ∧ p.bits.length≤128*(C.encode.length+1)+8 ∧
          ∃ a : List (Fin n × ℤ),(encodeSparseAssignment a).length≤polyBound 32 2 C.encode.length ∧
            (MvPolynomial.eval (sparseAssignmentPoint a) (circuitJacobianIntegerMinor C o v) : ZMod p)≠0 := by
  obtain ⟨r,hr,hrank⟩:=circuit_image_dimension_integer_minors C hvalid
  refine ⟨r,hr,?_⟩
  intro k
  constructor
  · intro hkr
    obtain ⟨o,v,ho,hv,hN⟩:=(hrank k).mp hkr
    refine ⟨o,v,ho,hv,?_,?_⟩
    · intro j
      exact active_variable_index_bits_le C (v j) (circuitJacobianIntegerMinor_active_indices C hvalid o v hN j)
    · exact (circuitJacobianIntegerMinor_ne_zero_iff_sparse_modular C hvalid o v ho).mp hN
  · rintro ⟨o,v,ho,hv,hvbits,hw⟩
    exact (hrank k).mpr ⟨o,v,ho,hv,(circuitJacobianIntegerMinor_ne_zero_iff_sparse_modular C hvalid o v ho).mpr hw⟩

end APSCounting893.Main
end Component_59

open APSCounting893.Main
theorem solution {n : ℕ} (C : APSCounting893.Main.ArithmeticCircuit n)
    (hvalid : APSCounting893.Main.ValidCircuit .rational C) :
    ∃ r : ℕ,RSCapacity.algDim (APSCounting893.Main.imageClosure (APSCounting893.Main.rationalComplexPolynomials C))=
      ((r : ℕ∞) : WithBot ℕ∞) ∧
      ∀ k : ℕ,k≤r ↔ APSCounting893.Main.ModularJacobianCertificate C k := by
  exact APSCounting893.Main.bounded_modular_dimension_certificates_proof C hvalid
