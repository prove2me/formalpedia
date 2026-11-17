-- Prove2me | Definitions.Def_WitnessEncryption_Runtime_Core
-- name    : WitnessEncryption_Runtime_Core
-- status  : Definition
-- author  : @vigyan
-- created : 2026-11-16T10:42:53.066206+00:00
-- url     : https://prove2.me/theorems/af5aa09a-90f9-4050-80da-0552f4d2bac2
-- title:
--   Certified list realizers and polynomial resource bounds
-- statement:
--   Let $\alpha$ and $\beta$ be encoded data types, and write $\operatorname{vol}(x)$ for the size of the encoding of $x$. For a concrete stack-machine realizer $R$ of a function $f:\alpha\to\beta$, the predicate $\operatorname{Certified}(R)$ requires a common exponent $d\in\mathbb N$ and constants $C_T,C_V$ such that, for every input $x$,
--
--   $$R.\operatorname{time}(x)\le C_T(\operatorname{vol}(x)+2)^d,\qquad \operatorname{vol}(f(x))\le C_V(\operatorname{vol}(x)+2)^d.$$
--
--   The module establishes closure of this certificate under composition, pairing, extensional congruence, finite branching, and folds whose reachable prefix states have a polynomial volume bound. It provides concrete realizers for list head and tail, option extraction with a default, list reversal and concatenation, and mapping with a retained environment, together with their resource certificates. These certified program constructors form the shared runtime interface used by the witness-encryption circuit and rank-reduction algorithms.
-- source:
--   Runtime formalization supporting Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, Section 6.5 and Theorems 6.1/1.1; supplied paper https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf . Exact original modules WitnessEncryption/Runtime/Certified.lean (excluding the separate cookLevin theorem), ListPrimitives.lean, and ListMap.lean; unchanged declaration bodies, export SHA256 1ec08f1bdb5ed8826247b4f7df265314c8c08439ada2d0f444a2ee7c30c4d50e.

import Definitions.Def_OAIThreeMachineSched02

set_option autoImplicit false

section
-- Source: WitnessEncryption.Runtime.Certified

namespace WitnessEncryption.Runtime

open OAI.ThreeMachine.StackCompiler

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [Coding α] [Coding β] [Coding γ]

/-- Both actual machine charge and encoded output volume have polynomial bounds. -/
def Certified {f : α → β} (R : Realizer f) : Prop :=
  ∃ d : ℕ, Poly volume R.time d ∧ Poly volume (fun x => volume (f x)) d

namespace Certified
variable {f : α → β} {g : β → γ}

theorem congr {f' : α → β} {R : Realizer f}
    (hR : Certified R) (h : ∀ x, f x = f' x) : Certified (R.congr h) := by
  rcases hR with ⟨d, ht, hv⟩
  refine ⟨d, ht, ?_⟩
  simpa only [← h] using hv

theorem comp {R : Realizer f} {S : Realizer g}
    (hR : Certified R) (hS : Certified S) : Certified (R.comp S) := by
  rcases hR with ⟨d, ht, hv⟩
  rcases hS with ⟨e, hs, hw⟩
  have hs' := Poly.reparam hs f hv
  have hw' := Poly.reparam hw f hv
  let D := max d (e*d)
  have hd : d ≤ D := Nat.le_max_left _ _
  have he : e*d ≤ D := Nat.le_max_right _ _
  have htime : Poly volume R.time D := ht.lift hd
  have hnext : Poly volume (fun x => S.time (f x)) D := hs'.lift he
  have hvol : Poly volume (fun x => volume (f x)) D := hv.lift hd
  have hover : Poly volume (fun x => 10*(volume (f x)+1)) D := by
    simpa using ((OAI.ThreeMachine.StackCompiler.Poly.const volume 10).mul (hvol.add (OAI.ThreeMachine.StackCompiler.Poly.const volume 1)))
  refine ⟨D, ?_, hw'.lift he⟩
  exact Poly.of_le (fun x => le_of_eq (Realizer.time_comp R S x))
    (by simpa only [Nat.max_self, Nat.max_zero, Nat.zero_add] using (htime.add hnext).add hover)

theorem pair {g : α → γ} {R : Realizer f} {S : Realizer g}
    (hR : Certified R) (hS : Certified S) : Certified (R.pair S) := by
  rcases hR with ⟨d, ht, hv⟩
  rcases hS with ⟨e, hs, hw⟩
  let D := max d (max e 1)
  have hd : d ≤ D := by dsimp [D]; omega
  have he : e ≤ D := by dsimp [D]; omega
  have h1 : 1 ≤ D := by dsimp [D]; omega
  have ht' := ht.lift hd
  have hs' := hs.lift he
  have hv' := hv.lift hd
  have hw' := hw.lift he
  have hx : Poly volume (volume : α → ℕ) D := (Poly.size volume).lift h1
  have ho : Poly volume (fun x => 20*(volume x+volume (f x)+volume (g x)+1)) D := by
    simpa only [Nat.max_self, Nat.max_zero, Nat.zero_add] using (OAI.ThreeMachine.StackCompiler.Poly.const volume 20).mul
      (((hx.add hv').add hw').add (OAI.ThreeMachine.StackCompiler.Poly.const volume 1))
  refine ⟨D, ?_, ?_⟩
  · exact Poly.of_le (fun x => le_of_eq (Realizer.time_pair R S x))
      (by simpa only [Nat.max_self, Nat.max_zero, Nat.zero_add] using (ht'.add hs').add ho)
  · simpa only [volume_pair, Nat.max_self, Nat.max_zero, Nat.zero_add] using (hv'.add hw').add (OAI.ThreeMachine.StackCompiler.Poly.const volume 1)

theorem identity : Certified (Realizer.id : Realizer (_root_.id : α → α)) := by
  refine ⟨1, ?_, Poly.size volume⟩
  exact Poly.of_le (fun x => le_of_eq (Realizer.time_id x)) (Poly.base (volume : α → ℕ))

theorem fst : Certified (Realizer.fst : Realizer (Prod.fst : α × β → α)) := by
  refine ⟨1, ?_, ?_⟩
  · exact Poly.of_le (fun x => le_of_eq (Realizer.time_fst x)) (Poly.base (volume : α × β → ℕ))
  · exact Poly.of_le (fun (x : α × β) => by rw [volume_pair]; omega) (Poly.size volume)

theorem snd : Certified (Realizer.snd : Realizer (Prod.snd : α × β → β)) := by
  refine ⟨1, ?_, ?_⟩
  · exact Poly.of_le (fun x => le_of_eq (Realizer.time_snd x)) (Poly.base (volume : α × β → ℕ))
  · exact Poly.of_le (fun (x : α × β) => by rw [volume_pair]; omega) (Poly.size volume)

theorem reinterpret (f : α → β) (h : ∀ x, enc (f x) = enc x) :
    Certified (Realizer.reinterpret f h) := by
  refine ⟨1, ?_, ?_⟩
  · exact Poly.of_le (fun x => le_of_eq (Realizer.time_reinterpret f h x)) (Poly.base (volume : α → ℕ))
  · have hv : ∀ x, volume (f x) = volume x := fun x => congrArg Data.size (h x)
    simpa only [hv] using Poly.size (volume : α → ℕ)

theorem constant (b : β) : Certified (Realizer.constant b : Realizer (fun _ : α => b)) := by
  refine ⟨1, ?_, (OAI.ThreeMachine.StackCompiler.Poly.const volume (volume b)).lift (by omega)⟩
  change Poly volume (fun x => (2*volume b+1)*(20*volume x+50*volume b+50)) 1
  have ht := (OAI.ThreeMachine.StackCompiler.Poly.const (volume : α → ℕ) (2*volume b+1)).mul
    ((((OAI.ThreeMachine.StackCompiler.Poly.const volume 20).mul (Poly.size volume)).add
      (OAI.ThreeMachine.StackCompiler.Poly.const volume (50*volume b))).add (OAI.ThreeMachine.StackCompiler.Poly.const volume 50))
  simpa using ht

theorem of_finite [Fintype α] {f : α → β} (R : Realizer f) : Certified R := by
  classical
  let T := Finset.univ.sup R.time
  let V := Finset.univ.sup (fun x => volume (f x))
  refine ⟨0, Poly.of_le (fun x => ?_) (OAI.ThreeMachine.StackCompiler.Poly.const volume T),
    Poly.of_le (fun x => ?_) (OAI.ThreeMachine.StackCompiler.Poly.const volume V)⟩
  · exact Finset.le_sup (f := R.time) (Finset.mem_univ x)
  · exact Finset.le_sup (f := fun x => volume (f x)) (Finset.mem_univ x)

end Certified

theorem length_le_volume (xs : List α) : xs.length ≤ volume xs := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.length_cons, volume_cons]; omega

/-- Charge an actual fold trace using its reachable prefix states. -/
theorem foldTime_prefix_bound {F : α × β → β} (R : Realizer F)
    (xs : List α) (b : β) (T V : ℕ)
    (hV : ∀ j, j ≤ xs.length →
      volume ((xs.take j).foldl (fun s a => F (a,s)) b) ≤ V)
    (hT : ∀ a ∈ xs, ∀ s, volume s ≤ V → R.time (a,s) ≤ T) :
    Realizer.foldTime R b xs ≤ xs.length*(T+20*(volume xs+2*V+1))+1 := by
  induction xs generalizing b with
  | nil => simp [Realizer.foldTime]
  | cons a xs ih =>
    have hb : volume b ≤ V := by simpa using hV 0 (by omega)
    have hs : volume (F (a,b)) ≤ V := by simpa using hV 1 (by simp)
    have hv : ∀ j, j ≤ xs.length →
        volume ((xs.take j).foldl (fun s a => F (a,s)) (F (a,b))) ≤ V := by
      intro j hj
      simpa only [List.take_succ_cons, List.foldl_cons] using hV (j+1) (by simp; omega)
    have ht := hT a (by simp) b hb
    have hi := ih (F (a,b)) hv (fun a ha => hT a (by simp [ha]))
    simp only [Realizer.foldTime, List.length_cons, volume_cons] at hi ⊢
    nlinarith [volume_pos a, volume_pos xs]

theorem time_fold_prefix_bound {F : α × β → β} (R : Realizer F)
    (xs : List α) (b : β) (T V : ℕ)
    (hV : ∀ j, j ≤ xs.length →
      volume ((xs.take j).foldl (fun s a => F (a,s)) b) ≤ V)
    (hT : ∀ a ∈ xs, ∀ s, volume s ≤ V → R.time (a,s) ≤ T) :
    R.fold.time (xs,b) ≤ 50*(xs.length+1)*(T+volume xs+V+1) := by
  have hh := foldTime_prefix_bound R xs b T V hV hT
  have hb : volume b ≤ V := by simpa using hV 0 (by omega)
  rw [Realizer.time_fold, volume_pair]
  nlinarith [volume_pos xs]

namespace Certified

/-- The finite conditional is charged for both compiled branches. -/
theorem choose {f g : α → β} {R : Realizer f} {S : Realizer g}
    (hR : Certified R) (hS : Certified S) : Certified (R.choose S) := by
  have ha : Certified ((Realizer.snd : Realizer (Prod.snd : Bool × α → α)).comp R) := snd.comp hR
  have hb : Certified ((Realizer.snd : Realizer (Prod.snd : Bool × α → α)).comp S) := snd.comp hS
  rcases ha with ⟨d, ht, hv⟩
  rcases hb with ⟨e, hs, hw⟩
  let D := max d (max e 1)
  have hd : d ≤ D := by dsimp [D]; omega
  have he : e ≤ D := by dsimp [D]; omega
  have h1 : 1 ≤ D := by dsimp [D]; omega
  have ht' := ht.lift hd
  have hs' := hs.lift he
  have hv' := hv.lift hd
  have hw' := hw.lift he
  have hx : Poly volume (volume : Bool × α → ℕ) D := (Poly.size volume).lift h1
  have ho : Poly volume (fun x : Bool × α =>
      30*(volume x+volume (f x.2)+volume (g x.2)+1)) D := by
    simpa only [Function.comp_apply, Nat.max_self, Nat.max_zero, Nat.zero_add] using
      (OAI.ThreeMachine.StackCompiler.Poly.const volume 30).mul
        (((hx.add hv').add hw').add (OAI.ThreeMachine.StackCompiler.Poly.const volume 1))
  refine ⟨D, ?_, ?_⟩
  · exact Poly.of_le (fun x => le_of_eq (Realizer.time_choose R S x))
      (by simpa only [Nat.max_self] using (ht'.add hs').add ho)
  · apply Poly.of_le (g := fun x : Bool × α => volume (f x.2)+volume (g x.2))
    · intro x; change volume (if x.1 then f x.2 else g x.2) ≤ _
      split <;> omega
    · simpa only [Function.comp_apply, Nat.max_self] using hv'.add hw'

/-- Polynomially bounded prefix states turn a concrete fold realizer into a
polynomial-time realizer. The hypothesis is a semantic space invariant, while
the conclusion bounds the charge of the compiled loop itself. -/
theorem fold {F : α × β → β} {R : Realizer F} (hR : Certified R)
    (hV : ∃ C k : ℕ, ∀ (x : List α × β) (j : ℕ), j ≤ x.1.length →
      volume ((x.1.take j).foldl (fun s a => F (a,s)) x.2) ≤ C*(volume x+2)^k) :
    Certified R.fold := by
  rcases hR with ⟨d, ⟨D,hD⟩, _⟩
  rcases hV with ⟨C,k,hC⟩
  let size : List α × β → ℕ := volume
  let V : List α × β → ℕ := fun x => C*(size x+2)^k
  let T : List α × β → ℕ := fun x => D*(size x+V x+3)^d
  have hx : Poly size (fun x => volume x.1) 1 :=
    Poly.of_le (fun x => by change volume x.1 ≤ volume x; rw [volume_prod]; omega) (Poly.size size)
  have hl : Poly size (fun x => x.1.length) 1 :=
    Poly.of_le (fun x => length_le_volume x.1) hx
  have hv : Poly size V k := Poly.powerBase size C k
  have hsum : Poly size (fun x => size x+V x+3) (max 1 k) := by
    simpa only [Nat.max_zero] using ((Poly.size size).add hv).add
      (OAI.ThreeMachine.StackCompiler.Poly.const size 3)
  have ht : Poly size T ((max 1 k)*d) := by
    simpa only [Nat.zero_add] using (OAI.ThreeMachine.StackCompiler.Poly.const size D).mul (hsum.pow d)
  have hbound := (OAI.ThreeMachine.StackCompiler.Poly.const size 50).mul
    ((hl.add (OAI.ThreeMachine.StackCompiler.Poly.const size 1)).mul
      (((ht.add hx).add hv).add (OAI.ThreeMachine.StackCompiler.Poly.const size 1)))
  have htime := Poly.of_le (g := fun x => 50*(x.1.length+1)*(T x+volume x.1+V x+1))
    (fun (x : List α × β) => time_fold_prefix_bound R x.1 x.2 (T x) (V x)
      (fun j hj => hC x j hj) (by
        intro a ha s hs
        have hmem := volume_mem_le ha
        have hxs : volume x.1 ≤ size x := by dsimp [size]; rw [volume_prod]; omega
        exact (hD (a,s)).trans (Nat.mul_le_mul_left D
          (Nat.pow_le_pow_left (by rw [volume_pair]; omega) d))))
    (by simpa only [Nat.mul_assoc] using hbound)
  have hout : Poly size
      (fun x : List α × β => volume (x.1.foldl (fun s a => F (a,s)) x.2)) k :=
    Poly.of_le (fun x => by simpa only [List.take_length, V, size] using hC x x.1.length (by omega)) hv
  exact ⟨_, htime.lift (Nat.le_max_left _ _), hout.lift (Nat.le_max_right _ _)⟩



end Certified
end WitnessEncryption.Runtime

end

section
-- Source: WitnessEncryption.Runtime.ListPrimitives

namespace WitnessEncryption.Runtime.ListPrimitives
open OAI.ThreeMachine.StackCompiler

universe u v
variable {α : Type u} {β : Type v} [Coding α] [Coding β]

def headR : Realizer (List.head? : List α → Option α) :=
  (Uniform.head? : Uniform (fun (_ : Unit) (xs : List α) => xs.head?)).specialize ()

def tailR : Realizer (List.tail : List α → List α) :=
  (Uniform.tail : Uniform (fun (_ : Unit) (xs : List α) => xs.tail)).specialize ()

def getDR : Realizer (fun x : Option α × α => x.1.getD x.2) :=
  (Uniform.getD : Uniform (fun (_ : Unit) (x : Option α × α) => x.1.getD x.2)).specialize ()

def reverseR : Realizer (List.reverse : List α → List α) := Realizer.reverse

theorem nil_certified : Certified (Realizer.nil : Realizer (fun _ : α => ([] : List β))) := by
  refine ⟨0, ?_, ?_⟩
  · change Poly volume (fun _ : α => 2) 0
    exact OAI.ThreeMachine.StackCompiler.Poly.const volume 2
  · change Poly volume (fun _ : α => 1) 0
    exact OAI.ThreeMachine.StackCompiler.Poly.const volume 1

theorem cons_certified : Certified (Realizer.cons : Realizer (fun x : α × List α => x.1 :: x.2)) :=
  Certified.reinterpret _ (fun _ => rfl)

theorem head_certified : Certified (headR : Realizer (List.head? : List α → Option α)) := by
  refine ⟨1, ?_, ?_⟩
  · apply Poly.of_le (g := fun xs : List α => 10000*(volume xs+1))
    · intro xs
      exact Uniform.time_head?_le (I := Unit) (α := fun _ => α) () xs
    · simpa only [Nat.max_zero, Nat.zero_add] using (OAI.ThreeMachine.StackCompiler.Poly.const volume 10000).mul
        ((Poly.size volume).add (OAI.ThreeMachine.StackCompiler.Poly.const volume 1))
  · apply Poly.of_le (g := fun xs : List α => volume xs+2)
    · intro xs
      cases xs with
      | nil => simp
      | cons a xs => simp only [List.head?_cons, volume_some, volume_cons]; omega
    · exact Poly.base volume

theorem tail_certified : Certified (tailR : Realizer (List.tail : List α → List α)) := by
  refine ⟨1, ?_, ?_⟩
  · exact Poly.of_le (fun xs => le_of_eq
      (Uniform.time_tail (I := Unit) (α := fun _ => α) () xs)) (Poly.base volume)
  · apply Poly.of_le (g := volume) _ (Poly.size volume)
    intro xs
    cases xs <;> simp only [List.tail_nil, List.tail_cons, volume_cons] <;> omega

theorem getD_certified : Certified (getDR : Realizer (fun x : Option α × α => x.1.getD x.2)) := by
  refine ⟨1, ?_, ?_⟩
  · apply Poly.of_le (g := fun x : Option α × α => 10000*(volume x+1))
    · intro x
      have hh : getDR.time x ≤ 10000*(volume x.1+volume x.2+1) :=
        Uniform.time_getD_le (I := Unit) (α := fun _ => α) () x.1 x.2
      exact hh.trans (by rw [volume_prod]; omega)
    · simpa only [Nat.max_zero, Nat.zero_add] using (OAI.ThreeMachine.StackCompiler.Poly.const volume 10000).mul
        ((Poly.size volume).add (OAI.ThreeMachine.StackCompiler.Poly.const volume 1))
  · apply Poly.of_le (g := volume) _ (Poly.size volume)
    rintro ⟨o,a⟩
    cases o <;> simp only [Option.getD_none, Option.getD_some, volume_pair, volume_some] <;> omega

theorem reverse_certified : Certified (reverseR : Realizer (List.reverse : List α → List α)) := by
  have hl : Poly volume (fun xs : List α => xs.length) 1 :=
    Poly.of_le length_le_volume (Poly.size volume)
  have hb := (OAI.ThreeMachine.StackCompiler.Poly.const volume 200).mul
    ((hl.add (OAI.ThreeMachine.StackCompiler.Poly.const volume 1)).mul
      ((Poly.size volume).add (OAI.ThreeMachine.StackCompiler.Poly.const volume 1)))
  refine ⟨2, ?_, ?_⟩
  · apply Poly.of_le (g := fun xs : List α => 200*(xs.length+1)*(volume xs+1))
    · intro xs
      exact Uniform.time_reverse (I := Unit) (α := fun _ => α) () xs
    · simpa only [Nat.zero_add, Nat.max_zero, Nat.mul_assoc] using hb
  · exact (Poly.of_le (fun xs => le_of_eq (volume_reverse xs)) (Poly.size volume)).lift (by omega)

def appendR : Realizer (fun x : List α × List α => x.1 ++ x.2) :=
  (((Realizer.fst.comp reverseR).pair Realizer.snd).comp Realizer.cons.fold).congr
    (fun x => by simp only [Function.comp_apply, Realizer.fold_cons_eq, List.reverse_reverse])

theorem append_certified : Certified (appendR : Realizer (fun x : List α × List α => x.1 ++ x.2)) := by
  have hf : Certified (Realizer.cons.fold : Realizer
      (fun x : List α × List α => x.1.foldl (fun ys a => a :: ys) x.2)) := by
    apply Certified.fold cons_certified
    refine ⟨1,1,?_⟩
    intro x j hj
    rw [Realizer.fold_cons_eq]
    have hv := volume_append (x.1.take j).reverse x.2
    have ht := volume_append (x.1.take j) (x.1.drop j)
    rw [List.take_append_drop] at ht
    rw [volume_reverse] at hv
    simp only [Nat.one_mul, pow_one, volume_prod]
    omega
  exact ((Certified.fst.comp reverse_certified).pair Certified.snd).comp hf |>.congr (fun x => by
    simp only [Function.comp_apply, Realizer.fold_cons_eq, List.reverse_reverse])

end WitnessEncryption.Runtime.ListPrimitives

end

section
-- Source: WitnessEncryption.Runtime.ListMap

namespace WitnessEncryption.Runtime.ListMap
open OAI.ThreeMachine.StackCompiler
open WitnessEncryption.Runtime.ListPrimitives
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w} [Coding α] [Coding β] [Coding γ]

def step (f : γ × α → β) (x : α × (γ × List β)) : γ × List β :=
  (x.2.1,f (x.2.1,x.1)::x.2.2)

theorem fold_correct (f : γ × α → β) (xs : List α) (env : γ) (acc : List β) :
    xs.foldl (fun s a => step f (a,s)) (env,acc) =
      (env,(xs.map (fun a => f (env,a))).reverse++acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a xs ih =>
    change xs.foldl (fun s a => step f (a,s)) (env,f (env,a)::acc) = _
    rw [ih]
    simp [List.reverse_cons,List.append_assoc]

theorem fold_volume (f : γ × α → β) (xs : List α) (env : γ) (acc : List β) (B : ℕ)
    (hB : ∀ a ∈ xs, volume (f (env,a)) ≤ B) :
    volume (xs.foldl (fun s a => step f (a,s)) (env,acc)) ≤
      volume (env,acc)+xs.length*(B+1) := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    have ha := hB a (by simp)
    have hh := ih (f (env,a)::acc) (fun b hb => hB b (by simp [hb]))
    change volume (xs.foldl (fun s a => step f (a,s)) (env,f (env,a)::acc)) ≤ _
    simp only [volume_prod,volume_cons,List.length_cons] at hh ⊢
    nlinarith

def stepR {f : γ × α → β} (F : Realizer f) : Realizer (step f) :=
  (Realizer.snd.comp Realizer.fst).pair
    (((((Realizer.snd.comp Realizer.fst).pair Realizer.fst).comp F).pair
      (Realizer.snd.comp Realizer.snd)).comp Realizer.cons)

theorem step_certified {f : γ × α → β} {F : Realizer f} (hF : Certified F) :
    Certified (stepR F) :=
  (Certified.snd.comp Certified.fst).pair
    (((((Certified.snd.comp Certified.fst).pair Certified.fst).comp hF).pair
      (Certified.snd.comp Certified.snd)).comp cons_certified)

theorem fold_certified {f : γ × α → β} {F : Realizer f} (hF : Certified F) :
    Certified (stepR F).fold := by
  apply Certified.fold (step_certified hF)
  obtain ⟨d,ht,hv⟩ := hF
  obtain ⟨C,hC⟩ := hv
  refine ⟨C+2,d+1,?_⟩
  intro x j hj
  let V := volume x
  let P := (V+2)^d
  have hpos : 1 ≤ P := by have hh : 0 < (V+2)^d := pow_pos (by omega) _; omega
  have hs : volume x.2 ≤ V := by dsimp [V]; simp only [volume_prod]; omega
  have hl : (x.1.take j).length ≤ V := by
    have hn := length_le_volume x.1
    have hp := List.length_take_le j x.1
    dsimp [V]; rw [volume_prod]; omega
  have hB : ∀ a ∈ x.1.take j, volume (f (x.2.1,a)) ≤ C*P := by
    intro a ha
    have hm := volume_mem_le (List.mem_of_mem_take ha)
    have hb : volume (x.2.1,a)+2 ≤ V+2 := by
      dsimp [V]; simp only [volume_prod]; omega
    exact (hC (x.2.1,a)).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hb d))
  have hf := fold_volume f (x.1.take j) x.2.1 x.2.2 (C*P) hB
  have hb : volume x.2+(x.1.take j).length*(C*P+1) ≤ V*(C*P+2) := by
    calc
      _ ≤ V+V*(C*P+1) := Nat.add_le_add hs (Nat.mul_le_mul_right (C*P+1) hl)
      _ = _ := by ring
  have hm : V*(C*P+2) ≤ (V+2)*((C+2)*P) := Nat.mul_le_mul (by omega) (by nlinarith)
  have he : (V+2)*((C+2)*P) = (C+2)*(volume x+2)^(d+1) := by
    dsimp [V,P]; rw [pow_succ]; ring
  exact hf.trans (hb.trans (hm.trans_eq he))

/-- An actual mapper whose dynamic environment is charged and retained by the code. -/
def mapR {f : γ × α → β} (F : Realizer f) :
    Realizer (fun x : γ × List α => x.2.map (fun a => f (x.1,a))) :=
  ((((Realizer.snd.pair (Realizer.fst.pair Realizer.nil)).comp (stepR F).fold).comp
    (Realizer.snd.comp reverseR))).congr (fun x => by
      have hh := congrArg (fun s : γ × List β => s.2.reverse) (fold_correct f x.2 x.1 [])
      simpa only [Function.comp_apply,List.append_nil,List.reverse_reverse] using hh)

theorem map_certified {f : γ × α → β} {F : Realizer f} (hF : Certified F) :
    Certified (mapR F) :=
  ((((Certified.snd.pair (Certified.fst.pair nil_certified)).comp (fold_certified hF)).comp
    (Certified.snd.comp reverse_certified))).congr (fun x => by
      have hh := congrArg (fun s : γ × List β => s.2.reverse) (fold_correct f x.2 x.1 [])
      simpa only [Function.comp_apply,List.append_nil,List.reverse_reverse] using hh)

end WitnessEncryption.Runtime.ListMap


end


