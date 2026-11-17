-- Prove2me | Definitions.Def_WitnessEncryption_Runtime_ListMetadataCompare
-- name    : WitnessEncryption_Runtime_ListMetadataCompare
-- status  : Definition
-- author  : @vigyan
-- created : 2026-11-16T11:48:11.859959+00:00
-- url     : https://prove2.me/theorems/429095d5-ca8f-4113-a235-36379bf781a8
-- title:
--   Certified list processing and binary comparison
-- statement:
--   This module supplies concrete polynomially certified realizers for list length, summation of unary-encoded natural numbers, and flattening a list of lists. It also supplies an environment-preserving filter: for a predicate $p:\eta\times\alpha\to\mathrm{Bool}$ with a given realizer $P$, the filter keeps the elements $a$ satisfying $p(e,a)=\mathrm{true}$, in their original order. If $P$ has a polynomial resource certificate, the resulting filter has one as well, with the environment $e$ included in the input size.
--
--   For a realizer $R$ of a function $f$, the certificate asserts that there are fixed $d,C_T,C_V\in\mathbb N$ such that every encoded input $x$ satisfies
--
--   $$R.\operatorname{time}(x)\le C_T(\operatorname{vol}(x)+2)^d,\qquad \operatorname{vol}(f(x))\le C_V(\operatorname{vol}(x)+2)^d.$$
--
--   The binary comparison routine operates directly on little-endian bit lists, allows zero padding, and compares their represented natural values. Its charged running time and output volume have polynomial bounds in the encoded input volume. Numeric bit-list values are used as a mathematical specification, rather than an efficient conversion to unary integers. The list and comparison interfaces are used by the sampling and feature-enumeration programs of the witness-encryption rank reduction.
-- source:
--   Runtime formalization supporting Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, Section 6.5 and Theorem 6.1; supplied paper https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf . Exact selected original declarations from WitnessEncryption/Runtime/Features/Metadata.lean and WitnessEncryption/Runtime/Binary/Compare.lean, with unchanged declaration bodies; export SHA256 b9fa21fd49c507f73ec78b47bafe3354ea80e720719032c7b6e4328579444eda.

import Definitions.Def_WitnessEncryption_Runtime_BinaryArithmetic

set_option autoImplicit false

section
-- Source: WitnessEncryption.Runtime.Features.Metadata

namespace WitnessEncryption.Runtime.FeatureMetadata
open OAI.ThreeMachine.StackCompiler
open WitnessEncryption.Runtime.ListPrimitives

theorem sub_certified : Certified Realizer.sub := by
  refine ⟨2,?_,?_⟩
  · apply Poly.of_le (g := fun x : ℕ × ℕ => 10000000*(volume x+2)^2)
    · intro x
      exact (Realizer.time_sub_le x.1 x.2).trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by rw [volume_prod,volume_nat,volume_nat]; omega) 2))
    · exact Poly.powerBase (volume : ℕ × ℕ → ℕ) 10000000 2
  · apply Poly.lift (d := 1) _ (by omega)
    apply Poly.of_le (g := volume) _ (Poly.size volume)
    intro x
    change volume (x.1-x.2) ≤ volume x
    simp only [volume_prod,volume_nat]
    omega

theorem count_fold {δ : Type*} (xs : List δ) (n : ℕ) :
    xs.foldl (fun n _ => n+1) n=n+xs.length := by
  induction xs generalizing n with
  | nil => simp
  | cons a xs ih => simp only [List.foldl_cons,ih,List.length_cons]; omega

def lengthR {δ : Type*} [Coding δ] : Realizer (List.length : List δ → ℕ) :=
  ((Realizer.id.pair (Realizer.constant 0)).comp (Realizer.snd.comp Realizer.succ).fold).congr
    (fun xs => by simp only [Function.comp_apply,id_eq,count_fold,Nat.zero_add])

theorem length_certified {δ : Type*} [Coding δ] :
    Certified (lengthR : Realizer (List.length : List δ → ℕ)) := by
  have hfold : Certified (Realizer.snd.comp Realizer.succ :
      Realizer (fun x : δ × ℕ => x.2+1)).fold := by
    apply Certified.fold (Certified.snd.comp NatPrimitives.succ_certified)
    refine ⟨3,1,?_⟩
    intro x j hj
    have hl := length_le_volume x.1
    have ht := List.length_take_le j x.1
    change volume ((x.1.take j).foldl (fun n (_ : δ) => n+1) x.2) ≤ _
    rw [count_fold]
    simp only [pow_one,volume_prod,volume_nat]
    omega
  exact ((Certified.identity.pair (Certified.constant 0)).comp hfold).congr
    (fun xs => by simp only [Function.comp_apply,id_eq,count_fold,Nat.zero_add])

theorem nat_sum_le_volume (xs : List ℕ) : xs.sum ≤ volume xs := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.sum_cons,volume_cons,volume_nat]; omega

theorem add_fold (xs : List ℕ) (n : ℕ) : xs.foldl (fun s a => a+s) n=n+xs.sum := by
  induction xs generalizing n with
  | nil => simp
  | cons a xs ih => simp only [List.foldl_cons,ih,List.sum_cons]; omega

def sumR : Realizer (List.sum : List ℕ → ℕ) :=
  ((Realizer.id.pair (Realizer.constant 0)).comp Realizer.add.fold).congr
    (fun xs => by simp only [Function.comp_apply,id_eq,add_fold,Nat.zero_add])

theorem sum_certified : Certified sumR := by
  have hfold : Certified Realizer.add.fold := by
    apply Certified.fold NatPrimitives.add_certified
    refine ⟨4,1,?_⟩
    intro x j hj
    have hsum := nat_sum_le_volume x.1
    have ht := congrArg List.sum (List.take_append_drop j x.1)
    rw [List.sum_append] at ht
    change volume ((x.1.take j).foldl (fun s a => a+s) x.2) ≤ _
    rw [add_fold]
    simp only [pow_one,volume_prod,volume_nat]
    omega
  exact ((Certified.identity.pair (Certified.constant 0)).comp hfold).congr
    (fun xs => by simp only [Function.comp_apply,id_eq,add_fold,Nat.zero_add])

universe u
variable {δ : Type u} [Coding δ]

theorem flatten_volume (xss : List (List δ)) : volume xss.flatten ≤ volume xss := by
  induction xss with
  | nil => exact le_rfl
  | cons xs xss ih =>
    have ha := volume_append xs xss.flatten
    simp only [List.flatten_cons,volume_cons] at ha ⊢
    omega

omit [Coding δ] in
theorem append_fold (xss : List (List δ)) (acc : List δ) :
    xss.foldl (fun acc xs => acc++xs) acc=acc++xss.flatten := by
  induction xss generalizing acc with
  | nil => simp
  | cons xs xss ih =>
    rw [List.foldl_cons,ih]
    simp only [List.flatten_cons,List.append_assoc]

def appendStepR : Realizer (fun x : List δ × List δ => x.2++x.1) :=
  (Realizer.snd.pair Realizer.fst).comp appendR

theorem appendFold_certified : Certified (appendStepR (δ := δ)).fold := by
  apply Certified.fold ((Certified.snd.pair Certified.fst).comp append_certified)
  refine ⟨2,1,?_⟩
  intro x j hj
  have ha := volume_append x.2 (x.1.take j).flatten
  have hf := flatten_volume (x.1.take j)
  have ht := volume_append (x.1.take j) (x.1.drop j)
  rw [List.take_append_drop] at ht
  have hp := volume_pos (x.1.drop j)
  change volume ((x.1.take j).foldl (fun acc xs => acc++xs) x.2) ≤ _
  rw [append_fold]
  simp only [pow_one,volume_prod]
  omega

def flattenR : Realizer (List.flatten : List (List δ) → List δ) :=
  ((Realizer.id.pair Realizer.nil).comp appendStepR.fold).congr
    (fun xss => by simp only [Function.comp_apply,id_eq,append_fold,List.nil_append])

theorem flatten_certified : Certified (flattenR (δ := δ)) :=
  ((Certified.identity.pair nil_certified).comp appendFold_certified).congr
    (fun xss => by simp only [Function.comp_apply,id_eq,append_fold,List.nil_append])

universe v
variable {η : Type v} [Coding η]

def filterStep (f : η × δ → Bool) (x : δ × (η × List δ)) : η × List δ :=
  (x.2.1,if f (x.2.1,x.1) then x.1::x.2.2 else x.2.2)

def filterStepR {f : η × δ → Bool} (P : Realizer f) : Realizer (filterStep f) :=
  (((((Realizer.snd.comp Realizer.fst).pair Realizer.fst).comp P).pair Realizer.id).comp
    (((Realizer.snd.comp Realizer.fst).pair
      ((Realizer.fst.pair (Realizer.snd.comp Realizer.snd)).comp Realizer.cons)).choose
        Realizer.snd)).congr (fun x => by
          by_cases h : f (x.2.1,x.1) <;> simp [filterStep,h])

theorem filterStep_certified {f : η × δ → Bool} {P : Realizer f} (hP : Certified P) :
    Certified (filterStepR P) := by
  have he : Certified (Realizer.snd.comp Realizer.fst :
      Realizer (fun x : δ × (η × List δ) => x.2.1)) := Certified.snd.comp Certified.fst
  have ha : Certified (Realizer.snd.comp Realizer.snd :
      Realizer (fun x : δ × (η × List δ) => x.2.2)) := Certified.snd.comp Certified.snd
  unfold filterStepR
  apply Certified.congr
  exact ((((he.pair Certified.fst).comp hP).pair Certified.identity).comp
    ((he.pair ((Certified.fst.pair ha).comp cons_certified)).choose Certified.snd))

omit [Coding δ] [Coding η] in
theorem filter_fold (f : η × δ → Bool) (xs : List δ) (env : η) (acc : List δ) :
    xs.foldl (fun s a => filterStep f (a,s)) (env,acc)=
      (env,(xs.filter (fun a => f (env,a))).reverse++acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons]
    by_cases h : f (env,a)
    · have hs : filterStep f (a,(env,acc))=(env,a::acc) := by simp [filterStep,h]
      rw [hs,ih]
      simp [h,List.reverse_cons,List.append_assoc]
    · have hs : filterStep f (a,(env,acc))=(env,acc) := by simp [filterStep,h]
      rw [hs,ih]
      simp [h]

omit [Coding η] in
theorem filter_volume (f : η × δ → Bool) (xs : List δ) (env : η) :
    volume (xs.filter (fun a => f (env,a))) ≤ volume xs := by
  induction xs with
  | nil => exact le_rfl
  | cons a xs ih =>
    by_cases h : f (env,a) <;> simp only [List.filter_cons,h] <;>
      simp only [Bool.false_eq_true,ite_true,ite_false,volume_cons] <;> omega

theorem filter_fold_volume (f : η × δ → Bool) (xs : List δ) (env : η) (acc : List δ) :
    volume (xs.foldl (fun s a => filterStep f (a,s)) (env,acc)) ≤ volume (env,acc)+volume xs := by
  rw [filter_fold]
  have ha := volume_append (xs.filter (fun a => f (env,a))).reverse acc
  have hf := filter_volume f xs env
  rw [volume_reverse] at ha
  simp only [volume_prod]
  omega

theorem filterFold_certified {f : η × δ → Bool} {P : Realizer f} (hP : Certified P) :
    Certified (filterStepR P).fold := by
  apply Certified.fold (filterStep_certified hP)
  refine ⟨2,1,?_⟩
  intro x j hj
  have hf := filter_fold_volume f (x.1.take j) x.2.1 x.2.2
  change volume ((x.1.take j).foldl (fun s a => filterStep f (a,s)) x.2) ≤
    volume x.2+volume (x.1.take j) at hf
  have ht := volume_append (x.1.take j) (x.1.drop j)
  rw [List.take_append_drop] at ht
  have hp := volume_pos (x.1.drop j)
  change volume ((x.1.take j).foldl (fun s a => filterStep f (a,s)) x.2) ≤ _
  simp only [pow_one,volume_prod] at hf ⊢
  omega

def filterR {f : η × δ → Bool} (P : Realizer f) :
    Realizer (fun x : η × List δ => x.2.filter (fun a => f (x.1,a))) :=
  ((((Realizer.snd.pair (Realizer.fst.pair Realizer.nil)).comp (filterStepR P).fold).comp
    (Realizer.snd.comp reverseR))).congr (fun x => by
      have h := congrArg (fun s : η × List δ => s.2.reverse) (filter_fold f x.2 x.1 [])
      simpa only [Function.comp_apply,id_eq,List.append_nil,List.reverse_reverse] using h)

theorem filter_certified {f : η × δ → Bool} {P : Realizer f} (hP : Certified P) :
    Certified (filterR P) :=
  ((((Certified.snd.pair (Certified.fst.pair nil_certified)).comp (filterFold_certified hP)).comp
    (Certified.snd.comp reverse_certified))).congr (fun x => by
      have h := congrArg (fun s : η × List δ => s.2.reverse) (filter_fold f x.2 x.1 [])
      simpa only [Function.comp_apply,id_eq,List.append_nil,List.reverse_reverse] using h)

























end WitnessEncryption.Runtime.FeatureMetadata

end

section
-- Source: WitnessEncryption.Runtime.Binary.Compare

namespace WitnessEncryption.Runtime.Binary
open OAI.ThreeMachine.StackCompiler
namespace CompareProof

abbrev State := List Bool × Bool
abbrev StepInput := Bool × State

def advance (x y lower : Bool) : Bool := if x = y then lower else (!x && y)

def finish (s : State) : Bool := s.1.foldl (fun lower y => y || lower) s.2

def step (p : StepInput) : State :=
  (p.2.1.tail, advance p.1 (p.2.1.head?.getD false) p.2.2)

def aux (lower : Bool) : List Bool → List Bool → Bool
  | [], ys => finish (ys,lower)
  | x :: xs, ys => aux (advance x (ys.head?.getD false) lower) xs ys.tail







def advanceR : Realizer (fun p : Bool × (Bool × Bool) => advance p.1 p.2.1 p.2.2) :=
  (((Realizer.id : Realizer (_root_.id : Bool → Bool)).choose (Realizer.constant false)).choose
    ((Realizer.constant true).choose Realizer.id)).congr (fun p => by
      rcases p with ⟨x,y,b⟩
      cases x <;> cases y <;> rfl)

def ysR : Realizer (fun p : StepInput => p.2.1) := Realizer.snd.comp Realizer.fst

def lowerR : Realizer (fun p : StepInput => p.2.2) := Realizer.snd.comp Realizer.snd

def headValueR : Realizer (fun p : StepInput => p.2.1.head?.getD false) :=
  ((ysR.comp ListPrimitives.headR).pair (Realizer.constant false)).comp ListPrimitives.getDR

def advanceInputR : Realizer (fun p : StepInput => (p.1,(p.2.1.head?.getD false,p.2.2))) :=
  Realizer.fst.pair (headValueR.pair lowerR)

def stepR : Realizer step :=
  ((ysR.comp ListPrimitives.tailR).pair (advanceInputR.comp advanceR)).congr (fun _ => rfl)

theorem ysR_certified : Certified ysR := Certified.snd.comp Certified.fst

theorem lowerR_certified : Certified lowerR := Certified.snd.comp Certified.snd

theorem headValueR_certified : Certified headValueR :=
  ((ysR_certified.comp ListPrimitives.head_certified).pair (Certified.constant false)).comp
    ListPrimitives.getD_certified

theorem advanceInputR_certified : Certified advanceInputR :=
  Certified.fst.pair (headValueR_certified.pair lowerR_certified)

theorem stepR_certified : Certified stepR := by
  unfold stepR
  apply Certified.congr
  exact (ysR_certified.comp ListPrimitives.tail_certified).pair
    (advanceInputR_certified.comp (Certified.of_finite advanceR))

theorem tail_volume_le (ys : List Bool) : volume ys.tail ≤ volume ys := by
  cases ys <;> simp only [List.tail_nil, List.tail_cons, volume_nil, volume_cons] <;> omega

theorem fold_list_volume (xs : List Bool) (s : State) :
    volume ((xs.foldl (fun s x => step (x,s)) s).1) ≤ volume s.1 := by
  induction xs generalizing s with
  | nil => exact le_rfl
  | cons a xs ih =>
      exact (ih (step (a,s))).trans (tail_volume_le s.1)

theorem fold_step_certified : Certified stepR.fold := by
  apply Certified.fold stepR_certified
  refine ⟨4,1,?_⟩
  intro x j hj
  have hl := fold_list_volume (x.1.take j) x.2
  have hb := volume_bool ((x.1.take j).foldl (fun s a => step (a,s)) x.2).2
  simp only [pow_one, volume_prod] at hl hb ⊢
  omega

theorem finish_certified : Certified (Realizer.or.fold : Realizer finish) := by
  apply Certified.fold (Certified.of_finite Realizer.or)
  refine ⟨3,0,?_⟩
  intro x j hj
  simpa using volume_bool ((x.1.take j).foldl (fun s a => a || s) x.2)

def prepareR : Realizer (fun p : List Bool × List Bool => (p.1,(p.2,false))) :=
  Realizer.fst.pair (Realizer.snd.pair (Realizer.constant false))

theorem prepareR_certified : Certified prepareR :=
  Certified.fst.pair (Certified.snd.pair (Certified.constant false))

end CompareProof

/-- Unsigned little-endian comparison, allowing arbitrary high zero padding. -/
def less (xs ys : List Bool) : Bool :=
  CompareProof.finish (xs.foldl (fun s x => CompareProof.step (x,s)) (ys,false))



def lessR : Realizer (fun p : List Bool × List Bool => less p.1 p.2) :=
  ((CompareProof.prepareR.comp CompareProof.stepR.fold).comp Realizer.or.fold).congr (fun _ => rfl)

theorem less_certified : Certified lessR := by
  unfold lessR
  apply Certified.congr
  exact (CompareProof.prepareR_certified.comp CompareProof.fold_step_certified).comp
    CompareProof.finish_certified

end WitnessEncryption.Runtime.Binary


end


