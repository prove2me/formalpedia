-- Prove2me | Definitions.Def_OAI_AlternatingFlow_Part07
-- name    : OAI_AlternatingFlow_Part07
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T03:39:55.592589+00:00
-- url     : https://prove2.me/theorems/bee9dcde-b18d-464a-b3c8-17161cc045c8
-- title:
--   Alternating-flow construction, part 7 of 11 (port of OpenAI's formalization): typed programs, jet names, jet programs and field programs
-- statement:
--   Part 7 of 11 of a port of OpenAI's Lean formalization of the alternating-flow construction from the manuscript *Computation under Rapidly Vanishing Navier–Stokes Forcing* (OpenAI, September 27, 2026). This part contains typed programs, jet names, jet programs and field programs.
--
--   **Attribution.** The code is adapted verbatim from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, modules `TypedPrograms`, `JetNames`, `JetPrograms`, `FieldPrograms` of `lean/OAI/MathematicalPhysics/AlternatingFlow`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order with their imports replaced by the previous part. The model definitions come from the platform definition `NavierStokesAlternating`. Part 1 adds compatibility shims for three core lemmas renamed after Lean 4.33.1, and part 3 adjusts one side-goal tactic for Mathlib 0df444a.
--
--   The development is split into eleven parts only so that each compiles within the platform's time limit. Together the parts supply the velocity construction used to prove `OAI.AlternatingNS.velocity_construction`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/MathematicalPhysics/AlternatingFlow: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/TypedPrograms.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/JetNames.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/JetPrograms.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/FieldPrograms.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf

/-
Alternating-flow construction (port of OpenAI's formalization), part 7 of 11: typed programs, jet names, jet programs and field programs.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/MathematicalPhysics/AlternatingFlow/: TypedPrograms.lean, JetNames.lean, JetPrograms.lean, FieldPrograms.lean
These files formalize the manuscript "Computation under Rapidly Vanishing Navier-Stokes Forcing"
(OpenAI, September 27, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions come from the platform definition `NavierStokesAlternating`.
-/
import Mathlib
import Definitions.Def_OAI_AlternatingFlow_Part06

set_option autoImplicit false

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/TypedPrograms.lean =====
namespace OAI

section TypedProgramsDevelopment

namespace AlternatingNS.Effective

open Encodable

def execute {A B : Type*} [Encodable A] [Encodable B] (c : Program) (a : A) : Part B :=
  (c.eval (encode a)).bind (fun n => Part.ofOption (decode n))

lemma execute_partrec {A B : Type*} [Primcodable A] [Primcodable B] :
    Partrec₂ (@execute A B _ _) := by
  exact (Nat.Partrec.Code.eval_part.comp Computable.fst
    (Computable.encode.comp Computable.snd)).bind
    (Computable.ofOption (Computable.decode.comp Computable.snd))

lemma typed_fixedpoint {A B : Type*} [Primcodable A] [Primcodable B]
    (F : Program → A → Part B) (hF : Partrec₂ F) :
    ∃ c : Program, ∀ a, execute c a = F c a := by
  let G (c : Program) (n : ℕ) : Part ℕ :=
    (Part.ofOption (decode n)).bind (fun a : A => (F c a).map encode)
  have hG : Partrec₂ G := (Computable.ofOption (Computable.decode.comp Computable.snd)).bind
    ((hF.comp (Computable.fst.comp Computable.fst) Computable.snd).map
      (Computable.encode.comp Computable.snd))
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.fixed_point₂ hG
  refine ⟨c, fun a => ?_⟩
  simp [execute, hc, G, Part.bind_map]

lemma computable_of_execute {A B : Type*} [Primcodable A] [Primcodable B]
    (c : Program) (f : A → B) (h : ∀ a, f a ∈ execute c a) : Computable f :=
  (execute_partrec.comp (Computable.const c) Computable.id).of_eq_tot h

lemma partrec_ite {A B : Type*} [Primcodable A] [Primcodable B]
    (p : A → Prop) [DecidablePred p] (hp : Computable (fun a => decide (p a)))
    (f g : A → Part B) (hf : Partrec f) (hg : Partrec g) :
    Partrec (fun a => if p a then f a else g a) := by
  
  obtain ⟨cf,hcf⟩ := Nat.Partrec.Code.exists_code.mp hf
  obtain ⟨cg,hcg⟩ := Nat.Partrec.Code.exists_code.mp hg
  have hr : Partrec (fun a => execute (B := B) (if p a then cf else cg) a) :=
    execute_partrec.comp ((Computable.cond hp (Computable.const cf) (Computable.const cg)).of_eq
      (by simp)) Computable.id
  apply hr.of_eq
  intro a
  split_ifs <;> simp [execute, hcf, hcg, encodek, Part.bind_map]

lemma binary_recursive_program {A B : Type*} [Primcodable A] [Primcodable B]
    (p : A → Prop) [DecidablePred p] (hp : Computable (fun a => decide (p a)))
    (base : A → B) (hb : Computable base) (left right : A → A)
    (hl : Computable left) (hr : Computable right)
    (op : A × B × B → B) (ho : Computable op) :
    ∃ c : Program, ∀ a, execute c a =
      if p a then Part.some (base a) else
        (execute c (left a)).bind (fun u => (execute c (right a)).map (fun v => op (a,u,v))) := by
  let F (c : Program) (a : A) : Part B := if p a then Part.some (base a) else
    (execute c (left a)).bind (fun u => (execute c (right a)).map (fun v => op (a,u,v)))
  apply typed_fixedpoint F
  apply partrec_ite (p := fun z : Program × A => p z.2) (hp.comp Computable.snd)
  · exact hb.comp Computable.snd
  · have hrec₁ : Partrec (fun z : Program × A => execute (B := B) z.1 (left z.2)) :=
      execute_partrec.comp Computable.fst (hl.comp Computable.snd)
    have hrec₂ : Partrec (fun z : (Program × A) × B => execute (B := B) z.1.1 (right z.1.2)) :=
      execute_partrec.comp (Computable.fst.comp Computable.fst) (hr.comp (Computable.snd.comp Computable.fst))
    exact hrec₁.bind (hrec₂.map (ho.comp
      ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd))))

end AlternatingNS.Effective

end TypedProgramsDevelopment

end OAI


-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/JetNames.lean =====
namespace OAI

section JetNamesDevelopment

open scoped BigOperators Topology ContDiff
open Filter
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

noncomputable def direction (i : Fin 4) : ℝ × Space :=
  ![(1,0), (0,e 0), (0,e 1), (0,e 2)] i

lemma direction_norm (i : Fin 4) : ‖direction i‖ ≤ 1 := by
  fin_cases i <;> simp [direction, Prod.norm_def, Bounds.norm_e]

def shift (i : Fin 4) (h : ℚ) (q : RationalPoint) : RationalPoint :=
  if i = 0 then (q.1+h,q.2) else
  if i = 1 then (q.1,q.2.1+h,q.2.2) else
  if i = 2 then (q.1,q.2.1,q.2.2.1+h,q.2.2.2) else
  (q.1,q.2.1,q.2.2.1,q.2.2.2+h)

lemma shift_computable : Computable (fun z : Fin 4 × ℚ × RationalPoint => shift z.1 z.2.1 z.2.2) := by
  have h0 : Computable (fun z : Fin 4 × ℚ × RationalPoint => z.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have h1 : Computable (fun z : Fin 4 × ℚ × RationalPoint => z.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have h2 : Computable (fun z : Fin 4 × ℚ × RationalPoint => z.2.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have h3 : Computable (fun z : Fin 4 × ℚ × RationalPoint => z.2.2.2.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hh : Computable (fun z : Fin 4 × ℚ × RationalPoint => z.2.1) := Computable.fst.comp Computable.snd
  have hi (i : Fin 4) : Computable (fun z : Fin 4 × ℚ × RationalPoint => decide (z.1 = i)) :=
    Primrec.eq.decide.to_comp.comp Computable.fst (Computable.const i)
  have hadd := Arithmetic.rat_add.to_comp
  exact (Computable.cond (hi 0) ((hadd.comp h0 hh).pair (h1.pair (h2.pair h3)))
    (Computable.cond (hi 1) (h0.pair ((hadd.comp h1 hh).pair (h2.pair h3)))
      (Computable.cond (hi 2) (h0.pair (h1.pair ((hadd.comp h2 hh).pair h3)))
        (h0.pair (h1.pair (h2.pair (hadd.comp h3 hh))))))).of_eq (by rintro ⟨i,h,q⟩; fin_cases i <;> rfl)

lemma shift_cast (i : Fin 4) (h : ℚ) (q : RationalPoint) :
    rationalPoint (shift i h q) = rationalPoint q + (h:ℝ) • direction i := by
  fin_cases i <;> ext j <;> simp [shift, rationalPoint, rationalVector, direction, e,
    EuclideanSpace.equiv] <;> fin_cases j <;> simp

noncomputable def wordJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × Space → E) : List (Fin 4) → ℝ × Space → E
  | [] => f
  | i::w => fun z => fderiv ℝ (wordJet f w) z (direction i)

lemma wordJet_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × Space → E} (hf : ContDiff ℝ ∞ f) (w : List (Fin 4)) :
    ContDiff ℝ ∞ (wordJet f w) := by
  induction w with
  | nil => exact hf
  | cons i w ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

lemma wordJet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × Space → E} (hf : ContDiff ℝ ∞ f) (w : List (Fin 4)) (r : ℕ) (z : ℝ × Space) :
    ‖iteratedFDeriv ℝ r (wordJet f w) z‖ ≤ ‖iteratedFDeriv ℝ (r+w.length) f z‖ := by
  induction w generalizing r with
  | nil => simp [wordJet]
  | cons i w ih =>
    apply (Bounds.norm_directional_iterated _ (wordJet_smooth hf w) (direction i) r z).trans
    apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (direction_norm i))
    have hi : r + (i :: w).length = r + 1 + w.length := by simp only [List.length_cons]; omega
    rw [hi]
    exact ih (r+1)

lemma jet_lipschitz {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (C : ℝ)
    (hC : ∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ C) (x y : E) :
    ‖f x - f y‖ ≤ C * ‖x-y‖ := by
  exact (convex_univ : Convex ℝ (Set.univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => by simpa only [norm_iteratedFDeriv_one] using hC x) (Set.mem_univ y) (Set.mem_univ x)

lemma difference_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C)
    (q v : E) (hv : ‖v‖ ≤ 1) {h : ℝ} (hh : 0 < h) :
    |fderiv ℝ f q v - (f (q+h•v)-f q)/h| ≤ C*h := by
  have hLip (x y : E) : ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x-y‖ :=
    jet_lipschitz (hf.fderiv_right (by simp)) C (fun x => by
      simpa only [norm_iteratedFDeriv_fderiv] using hbound x) x y
  have hdist : ‖(q+h•v)-q‖ ≤ h := by
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hh] using mul_le_mul_of_nonneg_left hv hh.le
  have hmv := (convex_closedBall q h).norm_image_sub_le_of_norm_fderiv_le'
    (f := f) (φ := fderiv ℝ f q) (x := q) (y := q+h•v)
    (fun x _ => hf.differentiable (by simp) x)
    (fun x hx => (hLip x q).trans (mul_le_mul_of_nonneg_left
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx) hC))
    (Metric.mem_closedBall_self hh.le) (by simpa [Metric.mem_closedBall, dist_eq_norm] using hdist)
  have hmv' : |f (q+h•v)-f q-h*fderiv ℝ f q v| ≤ C*h*h := by
    have hx := hmv.trans (mul_le_mul_of_nonneg_left hdist (mul_nonneg hC hh.le))
    simpa only [add_sub_cancel_left, map_smul, smul_eq_mul, Real.norm_eq_abs] using hx
  rw [← abs_neg, neg_sub, div_sub' hh.ne', abs_div, abs_of_pos hh, div_le_iff₀ hh]
  simpa only [one_mul, mul_comm] using hmv'

lemma tolerance_add (m n : ℕ) : (tolerance (m+n) : ℝ) = (tolerance m : ℝ)*(tolerance n : ℝ) := by
  simp [tolerance, pow_add]

lemma nat_mul_tolerance (n : ℕ) : (n:ℝ)*(tolerance n:ℝ) ≤ 1 := by
  have hn : (n:ℝ) ≤ 2^n := by exact_mod_cast n.lt_two_pow_self.le
  calc
    _ ≤ (2:ℝ)^n * (tolerance n:ℝ) := mul_le_mul_of_nonneg_right hn (tolerance_pos n).le
    _ = 1 := by simp [tolerance]

lemma difference_precision (C k : ℕ) : (C:ℝ)*(tolerance (k+1+C):ℝ) ≤ tolerance (k+1) := by
  rw [tolerance_add, mul_left_comm]
  exact mul_le_of_le_one_right (tolerance_pos _).le (nat_mul_tolerance C)

end AlternatingNS.Effective

end JetNamesDevelopment

end OAI


-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/JetPrograms.lean =====
namespace OAI

section JetProgramsDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*}

def jetApprox (b : (A × RationalPoint) × ℕ → ℚ) (B : A × ℕ → ℕ)
    (a : A) : List (Fin 4) → RationalPoint → ℕ → ℚ
  | [], q, k => b ((a,q),k)
  | i::w, q, k =>
    let n := k+1+B (a,w.length+2)
    let m := k+2+n
    (jetApprox b B a w (shift i (tolerance n) q) m - jetApprox b B a w q m) / tolerance n

attribute [local irreducible] jetApprox

lemma jetApprox_computable [Primcodable A] (b : (A × RationalPoint) × ℕ → ℚ) (B : A × ℕ → ℕ)
    (hb : Computable b) (hB : Computable B) :
    Computable (fun z : A × List (Fin 4) × RationalPoint × ℕ => jetApprox b B z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  let Q := A × List (Fin 4) × RationalPoint × ℕ
  let n (z : Q) := z.2.2.2+1+B (z.1,z.2.1.tail.length+2)
  let m (z : Q) := z.2.2.2+2+n z
  let left (z : Q) : Q := (z.1,z.2.1.tail,shift (z.2.1.head?.getD 0) (tolerance (n z)) z.2.2.1,m z)
  let right (z : Q) : Q := (z.1,z.2.1.tail,z.2.2.1,m z)
  have ha : Computable (fun z : Q => z.1) := Computable.fst
  have hw : Computable (fun z : Q => z.2.1) := Computable.fst.comp Computable.snd
  have hq : Computable (fun z : Q => z.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hk : Computable (fun z : Q => z.2.2.2) := Computable.snd.comp (Computable.snd.comp Computable.snd)
  have ht : Computable (fun z : Q => z.2.1.tail) := Primrec.list_tail.to_comp.comp hw
  have hn : Computable n := Primrec.nat_add.to_comp.comp (Computable.succ.comp hk)
    (hB.comp (ha.pair (Primrec.nat_add.to_comp.comp (Computable.list_length.comp ht) (Computable.const 2))))
  have hm : Computable m := Primrec.nat_add.to_comp.comp
    (Primrec.nat_add.to_comp.comp hk (Computable.const 2)) hn
  have he : Computable (fun z : Q => tolerance (n z)) := tolerance_primrec.to_comp.comp hn
  have hl : Computable left := ha.pair (ht.pair ((shift_computable.comp
    ((Computable.option_getD (Primrec.list_head?.to_comp.comp hw) (Computable.const 0)).pair
      (he.pair hq))).pair hm))
  have hr : Computable right := ha.pair (ht.pair (hq.pair hm))
  have hbase : Computable (fun z : Q => b ((z.1,z.2.2.1),z.2.2.2)) :=
    hb.comp ((ha.pair hq).pair hk)
  have hop : Computable (fun z : Q × ℚ × ℚ => (z.2.1-z.2.2)/tolerance (n z.1)) :=
    Arithmetic.rat_div.to_comp.comp (Arithmetic.rat_sub.to_comp.comp
      (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd))
      (he.comp Computable.fst)
  obtain ⟨c,hc⟩ := binary_recursive_program (fun z : Q => z.2.1 = [])
    (Primrec.eq.decide.to_comp.comp hw (Computable.const []))
    (fun z => b ((z.1,z.2.2.1),z.2.2.2)) hbase left right hl hr
    (fun z : Q × ℚ × ℚ => (z.2.1-z.2.2)/tolerance (n z.1)) hop
  apply computable_of_execute c
  rintro ⟨a,w,q,k⟩
  induction w generalizing q k with
  | nil => simp [hc, jetApprox]
  | cons i w ih =>
    rw [hc]
    simp only [List.cons_ne_nil, ite_false]
    apply Part.mem_bind_iff.mpr
    refine ⟨_, ih (shift i (tolerance (n (a,i::w,q,k))) q) (m (a,i::w,q,k)), ?_⟩
    apply (Part.mem_map_iff _).mpr
    refine ⟨_, ih q (m (a,i::w,q,k)), ?_⟩
    rw [jetApprox]
    rfl

lemma jetApprox_error (f : A → ℝ × Space → ℝ) (sf : ∀ a, ContDiff ℝ ∞ (f a))
    (b : (A × RationalPoint) × ℕ → ℚ) (B : A × ℕ → ℕ)
    (hb : ∀ a q k, |f a (rationalPoint q) - (b ((a,q),k) : ℝ)| ≤ tolerance k)
    (hB : ∀ a r z, ‖iteratedFDeriv ℝ r (f a) z‖ ≤ B (a,r)) :
    ∀ a w q k, |wordJet (f a) w (rationalPoint q) - (jetApprox b B a w q k : ℝ)| ≤ tolerance k := by
  intro a w
  induction w with
  | nil => simpa only [wordJet, jetApprox] using hb a
  | cons i w ih =>
    intro q k
    let C := B (a,w.length+2)
    let n := k+1+C
    let m := k+2+n
    have hd := difference_error (wordJet_smooth (sf a) w) (Nat.cast_nonneg C)
      (fun z => (wordJet_bound (sf a) w 2 z).trans (by rw [Nat.add_comm 2 w.length]; exact hB a (w.length+2) z))
      (rationalPoint q) (direction i) (direction_norm i) (tolerance_pos n)
    have he : |(wordJet (f a) w (rationalPoint (shift i (tolerance n) q)) - wordJet (f a) w (rationalPoint q)) /
        (tolerance n : ℝ) -
        ((jetApprox b B a w (shift i (tolerance n) q) m - jetApprox b B a w q m) / tolerance n : ℚ)| ≤
          2 * (tolerance m : ℝ) / tolerance n := by
      push_cast
      rw [← sub_div, abs_div, abs_of_pos (tolerance_pos n)]
      apply div_le_div_of_nonneg_right _ (tolerance_pos n).le
      calc
        _ = |(wordJet (f a) w (rationalPoint (shift i (tolerance n) q)) - (jetApprox b B a w (shift i (tolerance n) q) m : ℝ)) -
          (wordJet (f a) w (rationalPoint q) - (jetApprox b B a w q m : ℝ))| := by congr 1; ring
        _ ≤ _ := (abs_sub _ _).trans (by linarith [ih (shift i (tolerance n) q) m, ih q m])
    have hp : 2 * (tolerance m : ℝ) / tolerance n = tolerance (k+1) := by
      dsimp [m]
      rw [tolerance_add, mul_div_assoc, mul_div_cancel_right₀ _ (tolerance_pos n).ne']
      simp [tolerance, pow_add]; ring
    have hh := abs_sub_le (fderiv ℝ (wordJet (f a) w) (rationalPoint q) (direction i))
      ((wordJet (f a) w (rationalPoint (shift i (tolerance n) q)) - wordJet (f a) w (rationalPoint q))/(tolerance n : ℝ))
      (((jetApprox b B a w (shift i (tolerance n) q) m - jetApprox b B a w q m)/tolerance n : ℚ) : ℝ)
    rw [shift_cast] at he hh
    have hsum := hh.trans (add_le_add hd he)
    rw [hp] at hsum
    have hp' := difference_precision C k
    have ht : (tolerance (k+1) : ℝ)+(tolerance (k+1) : ℝ) = tolerance k := by simp [tolerance, pow_succ]; ring
    change |fderiv ℝ (wordJet (f a) w) (rationalPoint q) (direction i) - _| ≤ _
    unfold jetApprox
    exact hsum.trans (by linarith)

lemma named_wordJet [Primcodable A] {f : A → ℝ × Space → ℝ}
    (sf : ∀ a, ContDiff ℝ ∞ (f a))
    (hf : Named (fun z : A × RationalPoint => f z.1 (rationalPoint z.2)))
    (B : A × ℕ → ℕ) (hB : Computable B)
    (hbound : ∀ a r z, ‖iteratedFDeriv ℝ r (f a) z‖ ≤ B (a,r)) :
    Named (fun z : (A × List (Fin 4)) × RationalPoint => wordJet (f z.1.1) z.1.2 (rationalPoint z.2)) := by
  obtain ⟨b,hb,h⟩ := hf
  refine ⟨fun z => jetApprox b B z.1.1.1 z.1.1.2 z.1.2 z.2, ?_, ?_⟩
  · have hp : Computable (fun z : (((A × List (Fin 4)) × RationalPoint) × ℕ) =>
        (z.1.1.1,z.1.1.2,z.1.2,z.2)) :=
      (Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
          ((Computable.snd.comp Computable.fst).pair Computable.snd))
    have hg := jetApprox_computable (A := A) b B hb hB
    have hcomp := Computable.comp hg hp
    exact hcomp
  · rintro ⟨⟨a,w⟩,q⟩ k
    exact jetApprox_error f sf b B (fun a q k => h (a,q) k) hbound a w q k

end AlternatingNS.Effective

end JetProgramsDevelopment

end OAI


-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/FieldPrograms.lean =====
namespace OAI

section FieldProgramsDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A E F : Type*} [Primcodable A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def JetBound (f : A → E → F) : Prop :=
  (∀ a, ContDiff ℝ ∞ (f a)) ∧ ∃ B : A × ℕ → ℕ, Computable B ∧
    ∀ a r x, ‖iteratedFDeriv ℝ r (f a) x‖ ≤ B (a,r)

lemma Certified.jetBound {f : A → ℝ × Space → F} (hf : Certified f) : JetBound f := by
  obtain ⟨sf,B,hB,h⟩ := hf
  exact ⟨sf, fun z => B (z.1,0,z.2), hB.comp (Computable.fst.pair ((Computable.const 0).pair Computable.snd)),
    fun a r z => by simpa using h a 0 r z⟩

lemma JetBound.congr {f g : A → E → F} (hf : JetBound f) (h : ∀ a x, f a x = g a x) : JetBound g := by
  rwa [← funext (fun a => funext (h a))]

lemma JetBound.param {B : Type*} [Primcodable B] {f : A → E → F} (hf : JetBound f)
    {g : B → A} (hg : Computable g) : JetBound (fun b => f (g b)) := by
  obtain ⟨sf,C,hC,h⟩ := hf
  exact ⟨fun b => sf (g b), fun z => C (g z.1,z.2), hC.comp ((hg.comp Computable.fst).pair Computable.snd), fun b => h (g b)⟩

lemma JetBound.comp_unit {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : A → E → F} (hf : JetBound f) (L : A → G →L[ℝ] E) (hL : ∀ a, ‖L a‖ ≤ 1) :
    JetBound (fun a => f a ∘ L a) := by
  obtain ⟨sf,B,hB,h⟩ := hf
  refine ⟨fun a => (sf a).comp (L a).contDiff, B, hB, fun a r z => ?_⟩
  exact (Bounds.norm_comp_linear (f a) (sf a) (L a) r z).trans
    ((mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hL a))).trans (h a r _))

lemma JetBound.linear_unit {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : A → E → F} (hf : JetBound f) (L : A → F →L[ℝ] G) (hL : ∀ a, ‖L a‖ ≤ 1) :
    JetBound (fun a => L a ∘ f a) := by
  obtain ⟨sf,B,hB,h⟩ := hf
  refine ⟨fun a => (L a).contDiff.comp (sf a), B, hB, fun a r z => ?_⟩
  exact (Bounds.norm_postcomp_linear (f a) (sf a) (L a) r z).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (hL a)).trans (h a r z))

lemma Scaled.jetBound {s : A → ℕ → ℝ} {f : A → ℕ → E → F} (hf : Scaled s f)
    (hs : ∀ a n, 0 ≤ s a n) (S : A × ℕ → ℕ) (hS : Computable S)
    (sS : ∀ a n, s a n ≤ S (a,n)) : JetBound (fun a : A × ℕ => f a.1 a.2) := by
  obtain ⟨sf,B,hB,h⟩ := hf
  refine ⟨fun a => sf a.1 a.2, fun z => B (z.1.1,z.2) * S z.1 ^ z.2,
    Primrec.nat_mul.to_comp.comp
      (hB.comp ((Computable.fst.comp Computable.fst).pair Computable.snd))
      (nat_pow.to_comp.comp (hS.comp Computable.fst) Computable.snd), ?_⟩
  rintro ⟨a,n⟩ r x
  simpa only [Nat.cast_mul, Nat.cast_pow] using (h a r n x).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hs a n) (sS a n) r) (Nat.cast_nonneg _))

lemma norm_proj (i : Fin 3) : ‖PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa using PiLp.norm_apply_le x i)

lemma norm_fst : ‖ContinuousLinearMap.fst ℝ ℝ Space‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa using norm_fst_le x)

lemma norm_snd : ‖ContinuousLinearMap.snd ℝ ℝ Space‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa using norm_snd_le x)

lemma JetBound.named_wordJet {f : A → ℝ × Space → ℝ} (hf : JetBound f)
    (hn : Named (fun z : A × RationalPoint => f z.1 (rationalPoint z.2))) :
    Named (fun z : (A × List (Fin 4)) × RationalPoint => wordJet (f z.1.1) z.1.2 (rationalPoint z.2)) := by
  obtain ⟨sf,B,hB,h⟩ := hf
  exact AlternatingNS.Effective.named_wordJet sf hn B hB h

lemma JetBound.named_directional {f : A → ℝ × Space → ℝ} (hf : JetBound f)
    (hn : Named (fun z : A × RationalPoint => f z.1 (rationalPoint z.2)))
    (i : A → Fin 4) (hi : Computable i) :
    Named (fun z : A × RationalPoint => fderiv ℝ (f z.1) (rationalPoint z.2) (direction (i z.1))) := by
  have hw : Computable (fun z : A × RationalPoint => ((z.1,[i z.1]),z.2)) :=
    (Computable.fst.pair (Primrec.list_cons.to_comp.comp (hi.comp Computable.fst) (Computable.const []))).pair Computable.snd
  have hh := hf.named_wordJet hn |>.comp hw
  exact hh.congr (fun _ => rfl)

lemma Certified.sum3 {f : Fin 3 → A → ℝ × Space → F} (hf : ∀ i, Certified (f i)) :
    Certified (fun a z => ∑ i : Fin 3, f i a z) := by
  exact ((hf 0).add ((hf 1).add (hf 2))).congr (fun _ _ => by simp [Fin.sum_univ_succ])

lemma Certified.dx {f : A → Velocity} (hf : Certified (fun a => Function.uncurry (f a))) (i : Fin 3) :
    Certified (fun a => Function.uncurry (dx i (f a))) :=
  (hf.directional (fun _ => (0,e i)) (fun _ => by simp [Prod.norm_def, Bounds.norm_e])).congr
    (fun a z => (Bounds.dx_eq_full_directional (f a) (hf.1 a) i z).symm)

lemma Certified.fullDt {f : A → Velocity} (hf : Certified (fun a => Function.uncurry (f a))) :
    Certified (fun a => Function.uncurry (Analytic.fullDt (f a))) :=
  (hf.directional (fun _ => (1,0)) (fun _ => by simp [Prod.norm_def])).congr
    (fun a z => (Bounds.fullDt_eq_full_directional (f a) (hf.1 a) z).symm)

lemma Certified.component {f : A → ℝ × Space → Space} (hf : Certified f) (i : A → Fin 3) :
    Certified (fun a z => f a z (i a)) :=
  hf.linear (fun a => PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) (i a)) (fun _ => 1) (Computable.const 1) (fun a => by simpa using norm_proj (i a))

lemma Certified.advection {f : A → Velocity} (hf : Certified (fun a => Function.uncurry (f a))) :
    Certified (fun a => Function.uncurry (advection (f a))) := by
  have hi (i : Fin 3) := (hf.component (fun _ => i)).smul (hf.dx i)
  exact (Certified.sum3 hi).congr (fun a z => (Bounds.advection_eq_sum (f a) z.1 z.2).symm)

lemma Certified.laplacian {f : A → Velocity} (hf : Certified (fun a => Function.uncurry (f a))) :
    Certified (fun a => Function.uncurry (laplacian (f a))) := Certified.sum3 (fun i => (hf.dx i).dx i)

noncomputable def fullForce (ν : ℝ) (M : Machine) (w : List ℕ) : Velocity :=
  fun t x => Analytic.fullDt (Construction.velocity M w) t x + advection (Construction.velocity M w) t x -
    ν • laplacian (Construction.velocity M w) t x

lemma force_certified (ν : ℝ) : Certified (fun z : Machine × List ℕ => Function.uncurry (fullForce ν z.1 z.2)) := by
  obtain ⟨D,hD⟩ := exists_nat_ge |ν|
  exact (velocity_certified.fullDt.add velocity_certified.advection).sub (velocity_certified.laplacian.csmul ν D hD)

lemma fullForce_half (ν : ℝ) (M : Machine) (w : List ℕ) :
    Bounds.HalfEq (fullForce ν M w) (Construction.force ν M w) := by
  intro t ht x
  simp only [fullForce, Construction.force, residual]
  rw [Analytic.dt_eq_full _ (Construction.velocity_smooth M w) t ht x]

end AlternatingNS.Effective

end FieldProgramsDevelopment

end OAI


