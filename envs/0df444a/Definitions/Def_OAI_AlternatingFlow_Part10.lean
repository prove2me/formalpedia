-- Prove2me | Definitions.Def_OAI_AlternatingFlow_Part10
-- name    : OAI_AlternatingFlow_Part10
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T03:47:58.519168+00:00
-- url     : https://prove2.me/theorems/62b15492-f705-46c5-844f-50f1855a380e
-- title:
--   Alternating-flow construction, part 10 of 11 (port of OpenAI's formalization): compilers turning certified data into field programs
-- statement:
--   Part 10 of 11 of a port of OpenAI's Lean formalization of the alternating-flow construction from the manuscript *Computation under Rapidly Vanishing Navier–Stokes Forcing* (OpenAI, September 27, 2026). This part contains compilers turning certified data into field programs.
--
--   **Attribution.** The code is adapted verbatim from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, modules `Compilers` of `lean/OAI/MathematicalPhysics/AlternatingFlow`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order with their imports replaced by the previous part. The model definitions come from the platform definition `NavierStokesAlternating`. Part 1 adds compatibility shims for three core lemmas renamed after Lean 4.33.1, and part 3 adjusts one side-goal tactic for Mathlib 0df444a.
--
--   The development is split into eleven parts only so that each compiles within the platform's time limit. Together the parts supply the velocity construction used to prove `OAI.AlternatingNS.velocity_construction`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/MathematicalPhysics/AlternatingFlow: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/Compilers.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf

/-
Alternating-flow construction (port of OpenAI's formalization), part 10 of 11: compilers turning certified data into field programs.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/MathematicalPhysics/AlternatingFlow/: Compilers.lean
These files formalize the manuscript "Computation under Rapidly Vanishing Navier-Stokes Forcing"
(OpenAI, September 27, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions come from the platform definition `NavierStokesAlternating`.
-/
import Mathlib
import Definitions.Def_OAI_AlternatingFlow_Part09

set_option autoImplicit false

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Compilers.lean =====
namespace OAI

section CompilersDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*} [Primcodable A]

lemma space_norm_le_sum (v : Space) : ‖v‖ ≤ ∑ i : Fin 3, |v i| := by
  have he : (∑ i : Fin 3, v i • e i) = v := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply]
  calc
    ‖v‖ = ‖∑ i : Fin 3, v i • e i‖ := congrArg norm he.symm
    _ ≤ ∑ i : Fin 3, ‖v i • e i‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul, Bounds.norm_e, mul_one, Real.norm_eq_abs]

lemma rationalVector_error (q : RationalVector) (v : Space) (k : ℕ)
    (h : ∀ i, |v i - rationalVector q i| ≤ (tolerance (k+2) : ℝ)) :
    ‖rationalVector q - v‖ ≤ dyadicError k := by
  apply (space_norm_le_sum _).trans
  have hi (i : Fin 3) : |(rationalVector q-v) i| ≤ (tolerance (k+2) : ℝ) := by
    change |rationalVector q i-v i| ≤ _
    rw [abs_sub_comm]
    exact h i
  have hsum : (∑ i : Fin 3, |(rationalVector q-v) i|) ≤ 3 * (tolerance (k+2) : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin 3, (tolerance (k+2) : ℝ) := Finset.sum_le_sum (fun i _ => hi i)
      _ = _ := by simp
  apply hsum.trans
  simp only [tolerance_cast, dyadicError, pow_add]
  nlinarith [pow_pos (by norm_num : (0:ℝ)<1/2) k]

lemma mul_precision (C k : ℕ) : (C : ℝ) * (tolerance (k+C) : ℝ) ≤ tolerance k := by
  rw [tolerance_add, mul_left_comm]
  exact mul_le_of_le_one_right (tolerance_pos _).le (nat_mul_tolerance C)

abbrev EvalInput := ℕ × IndexCode × RationalPoint × ℕ
abbrev ModInput := ℕ × IndexCode × ℕ × ℕ
abbrev BoundInput := ℕ × ℕ × IndexCode

def sample (b : (((A × Fin 3) × List (Fin 4)) × RationalPoint) × ℕ → ℚ)
    (a : A) (q : EvalInput) (i : Fin 3) : ℚ :=
  b ((((a,i),mixedWord q.1 q.2.1),q.2.2.1),q.2.2.2+2)

def values (b : (((A × Fin 3) × List (Fin 4)) × RationalPoint) × ℕ → ℚ)
    (a : A) (q : EvalInput) : RationalVector :=
  (sample b a q 0,sample b a q 1,sample b a q 2)

lemma sample_computable (b : (((A × Fin 3) × List (Fin 4)) × RationalPoint) × ℕ → ℚ)
    (hb : Computable b) (i : Fin 3) : Computable₂ (fun a : A => fun q : EvalInput => sample b a q i) := by
  have hl : Computable (fun z : A × EvalInput => z.2.1) := Computable.fst.comp Computable.snd
  have hα : Computable (fun z : A × EvalInput => z.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hq : Computable (fun z : A × EvalInput => z.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hk : Computable (fun z : A × EvalInput => z.2.2.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  exact hb.comp ((((Computable.fst.pair (Computable.const i)).pair
    (mixedWord_computable.comp hl hα)).pair hq).pair
    (Primrec.nat_add.to_comp.comp hk (Computable.const 2)))

lemma values_computable (b : (((A × Fin 3) × List (Fin 4)) × RationalPoint) × ℕ → ℚ)
    (hb : Computable b) : Computable₂ (values b) :=
  (sample_computable b hb 0).pair ((sample_computable b hb 1).pair (sample_computable b hb 2))

def modulus (B : A × ℕ × ℕ → ℕ) (a : A) (q : ModInput) : ℕ :=
  q.2.2.2 + B (a,0,(mixedWord q.1 q.2.1).length+1)

lemma modulus_computable (B : A × ℕ × ℕ → ℕ) (hB : Computable B) : Computable₂ (modulus B) := by
  have hl : Computable (fun z : A × ModInput => z.2.1) := Computable.fst.comp Computable.snd
  have hα : Computable (fun z : A × ModInput => z.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hk : Computable (fun z : A × ModInput => z.2.2.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  exact Primrec.nat_add.to_comp.comp hk (hB.comp (Computable.fst.pair
    ((Computable.const 0).pair (Computable.succ.comp (Computable.list_length.comp
      (mixedWord_computable.comp hl hα))))))

def bound (B : A × ℕ × ℕ → ℕ) (a : A) (q : BoundInput) : ℕ :=
  B (a,q.1,(mixedWord q.2.1 q.2.2).length)

lemma bound_computable (B : A × ℕ × ℕ → ℕ) (hB : Computable B) : Computable₂ (bound B) := by
  have hJ : Computable (fun z : A × BoundInput => z.2.1) := Computable.fst.comp Computable.snd
  have hl : Computable (fun z : A × BoundInput => z.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hα : Computable (fun z : A × BoundInput => z.2.2.2) := Computable.snd.comp (Computable.snd.comp Computable.snd)
  exact hB.comp (Computable.fst.pair (hJ.pair
    (Computable.list_length.comp (mixedWord_computable.comp hl hα))))

lemma Certified.programs {f : A → Velocity}
    (hf : Certified (fun a => Function.uncurry (f a)))
    (hn : Named (fun z : (A × Fin 3) × RationalPoint =>
      f z.1.1 (rationalPoint z.2).1 (rationalPoint z.2).2 z.1.2)) :
    ∃ compile : A → FieldProgram, Computable compile ∧ ∀ a, ProgramFor (compile a) (f a) := by
  obtain ⟨b,hb,hbError⟩ := hf.jetBound.named_component_words hn
  obtain ⟨sf,B,hB,hBound⟩ := hf
  obtain ⟨ce,hce,he⟩ := compiler_of_computable (values b) (values_computable b hb)
  obtain ⟨cm,hcm,hm⟩ := compiler_of_computable (modulus B) (modulus_computable B hB)
  obtain ⟨cb,hcb,hc⟩ := compiler_of_computable (bound B) (bound_computable B hB)
  refine ⟨fun a => (ce a,cm a,cb a), hce.pair (hcm.pair hcb), fun a => ⟨?_,?_,?_⟩⟩
  · intro l α q k
    refine ⟨values b a (l,α,q,k),?_,fun ht => ?_⟩
    · have hh := he a (l,α,q,k)
      rcases q with ⟨t,x,y,z⟩
      simpa only [Returns, values, Encodable.encode_prod_val, Arithmetic.rationalCoding_encode] using hh
    · rw [mixed_eq_wordJet (f a) (sf a) l α _ (by change 0 ≤ (q.1 : ℝ); exact_mod_cast ht)]
      apply rationalVector_error
      intro i
      have hh := hbError (((a,i),mixedWord l α),q) (k+2)
      have heq : rationalVector (values b a (l,α,q,k)) i = (sample b a (l,α,q,k) i : ℝ) := by
        fin_cases i <;> rfl
      rw [heq]
      exact hh
  · intro l α R k
    refine ⟨modulus B a (l,α,R,k),hm a (l,α,R,k),fun z z' ht ht' _ _ hd => ?_⟩
    rw [mixed_eq_wordJet (f a) (sf a) l α z.1 ht z.2,
      mixed_eq_wordJet (f a) (sf a) l α z'.1 ht' z'.2]
    let C := B (a,0,(mixedWord l α).length+1)
    have hC (y : ℝ × Space) : ‖iteratedFDeriv ℝ 1 (wordJet (Function.uncurry (f a)) (mixedWord l α)) y‖ ≤ C := by
      have hC' : ‖iteratedFDeriv ℝ (1+(mixedWord l α).length) (Function.uncurry (f a)) y‖ ≤ C := by
        rw [Nat.add_comm 1 (mixedWord l α).length]
        simpa only [C, pow_zero, one_mul] using hBound a 0 ((mixedWord l α).length+1) y
      exact (wordJet_bound (sf a) (mixedWord l α) 1 y).trans hC'
    have hLip := jet_lipschitz (wordJet_smooth (sf a) (mixedWord l α)) C hC z z'
    exact hLip.trans ((mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg C)).trans (by
      simpa only [modulus, C, tolerance_cast] using mul_precision C k))
  · intro J l α
    refine ⟨bound B a (J,l,α),hc a (J,l,α),fun t ht x => ?_⟩
    rw [mixed_eq_wordJet (f a) (sf a) l α t ht x]
    have hnorm : ‖wordJet (Function.uncurry (f a)) (mixedWord l α) (t,x)‖ ≤
        ‖iteratedFDeriv ℝ (mixedWord l α).length (Function.uncurry (f a)) (t,x)‖ := by
      have hh := wordJet_bound (sf a) (mixedWord l α) 0 (t,x)
      rw [Nat.zero_add] at hh
      simpa only [norm_iteratedFDeriv_zero] using hh
    apply (mul_le_mul_of_nonneg_left hnorm (by positivity : (0:ℝ) ≤ (1+t+‖x‖)^J)).trans
    simpa only [bound, weight, abs_of_nonneg ht] using hBound a J (mixedWord l α).length (t,x)

end AlternatingNS.Effective

namespace AlternatingNS

lemma ProgramFor.congr_half {c : FieldProgram} {f g : Velocity}
    (hf : ProgramFor c f) (h : Bounds.HalfEq f g) : ProgramFor c g := by
  refine ⟨?_,?_,?_⟩
  · intro l α q k
    obtain ⟨v,hv,he⟩ := hf.1 l α q k
    refine ⟨v,hv,fun ht => ?_⟩
    rw [← h.mixed l (index α) _ (by change 0 ≤ (q.1 : ℝ); exact_mod_cast ht) _]
    exact he ht
  · intro l α R k
    obtain ⟨m,hm,he⟩ := hf.2.1 l α R k
    refine ⟨m,hm,fun z z' ht ht' hz hz' hd => ?_⟩
    rw [← h.mixed l (index α) _ ht _, ← h.mixed l (index α) _ ht' _]
    exact he z z' ht ht' hz hz' hd
  · intro J l α
    obtain ⟨B,hB,he⟩ := hf.2.2 J l α
    refine ⟨B,hB,fun t ht x => ?_⟩
    rw [← h.mixed l (index α) _ ht _]
    exact he t ht x

end AlternatingNS

end CompilersDevelopment

end OAI


