-- Prove2me | Definitions.Def_RandomDimReduction_Channel_BooleanPrograms
-- name    : RandomDimReduction_Channel_BooleanPrograms
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:28:09.947318+00:00
-- url     : https://prove2.me/theorems/ea29d695-48b6-4179-ac85-c99f58ebaeb1
-- title:
--   Boolean programs and their compilation to well-formed circuits
-- statement:
--   This module defines a small typed language of Boolean programs, with wire renaming, gates, pairing, and composition. It gives operational semantics and a gate-count function, proves the correctness and well-formedness of compilation into `QAlgorithms.BoolCircuit`, and supplies bounded-size constructors for Boolean operations, finite families, sums, and products. The final specification converts a `HasProgram` bound into a well-formed Boolean circuit with the same evaluation function and bounded size.
--
--   These definitions form the classical reversible-circuit foundation used by the efficient random dimension-reduction construction. **Formalization Note.** This is the recovered, sorry-free `Solutions.BooleanPrograms` module of submission `7d8da302-ad2d-4946-b139-915784e2b187`; its remote Lean check passed before publication.
-- source:
--   Angus Lowe and Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994, Theorem 1.1 p.2 and Section 5.2 pp.15–19; supporting classical circuit infrastructure recovered verbatim from failed prove2.me submission 7d8da302-ad2d-4946-b139-915784e2b187, module Solutions.BooleanPrograms (adapted there from accepted submission 63bb1527-8a3c-4873-a725-6590f479b916).

-- Recovered from failed submission 7d8da302-ad2d-4946-b139-915784e2b187,
-- module Solutions.BooleanPrograms.
import Definitions.Def_QAlgorithms_Defs_Classical
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.style.haveILetI false
set_option linter.defProp false

section p2mFlat_Solutions_BooleanPrograms

/- Adapted from the accepted proof of QAlgorithms.gf2_nullvector_circuit,
submission 63bb1527-8a3c-4873-a725-6590f479b916. -/
set_option autoImplicit false
noncomputable section
open QAlgorithms Classical
open scoped BigOperators
namespace RandomDimReduction.Channel.BooleanPrograms
@[simp] lemma bool_false : false = (0 : Bool) := rfl
@[simp] lemma bool_true : true = (1 : Bool) := rfl
@[simp] lemma bool_double (b : Bool) : b + b = 0 := BooleanRing.add_self b

inductive Program : Type → Type → Type 1
  | wire {ι κ : Type} (f : κ → ι) : Program ι κ
  | gate {ι : Type} (op : BoolOp) (a b : ι) : Program ι Unit
  | pair {ι κ τ : Type} : Program ι κ → Program ι τ → Program ι (Sum κ τ)
  | comp {ι κ τ : Type} : Program ι κ → Program κ τ → Program ι τ

def opValue (op : BoolOp) (a b : Bool) : Bool :=
  match op with | .and => a && b | .or => a || b | .not => !a

def Program.value {ι κ : Type} : Program ι κ → (ι → Bool) → κ → Bool
  | .wire f, x => x ∘ f
  | .gate op a b, x => fun _ => opValue op (x a) (x b)
  | .pair p q, x => Sum.elim (p.value x) (q.value x)
  | .comp p q, x => q.value (p.value x)

def Program.cost {ι κ : Type} : Program ι κ → ℕ
  | .wire _ => 0
  | .gate _ _ _ => 1
  | .pair p q => p.cost + q.cost
  | .comp p q => p.cost + q.cost

def values (xs : List Bool) (gs : List BoolGate) : List Bool :=
  gs.foldl (fun vs g => vs ++ [g.value vs]) xs

lemma values_length (xs : List Bool) (gs : List BoolGate) :
    (values xs gs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [values]
  | cons g gs ih => simpa [values, List.foldl_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (xs ++ [g.value xs])

lemma values_prefix (xs : List Bool) (gs : List BoolGate) {i : ℕ} (hi : i < xs.length) :
    (values xs gs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (values (xs ++ [g.value xs]) gs).getD i false = _
    rw [ih (xs ++ [g.value xs]) (by simp only [List.length_append, List.length_singleton]; omega)]
    exact List.getD_append xs _ false i hi

def Program.compile {ι κ : Type} : Program ι κ → ℕ → (ι → ℕ) → List BoolGate × (κ → ℕ)
  | .wire f, _, env => ([], env ∘ f)
  | .gate op a b, N, env => ([⟨op, env a, env b⟩], fun _ => N)
  | .pair p q, N, env =>
    let gs := (p.compile N env).1
    let out := (p.compile N env).2
    let hs := (q.compile (N + gs.length) env).1
    let out' := (q.compile (N + gs.length) env).2
    (gs ++ hs, Sum.elim out out')
  | .comp p q, N, env =>
    let gs := (p.compile N env).1
    let out := (p.compile N env).2
    let hs := (q.compile (N + gs.length) out).1
    let out' := (q.compile (N + gs.length) out).2
    (gs ++ hs, out')

def Good (N : ℕ) (gs : List BoolGate) : Prop :=
  ∀ k : Fin gs.length, (gs.get k).a < N + k ∧
    ((gs.get k).op = BoolOp.not ∨ (gs.get k).b < N + k)

lemma good_append {N : ℕ} {gs hs : List BoolGate}
    (hg : Good N gs) (hh : Good (N + gs.length) hs) : Good N (gs ++ hs) := by
  intro k
  by_cases h : k.val < gs.length
  · simpa [List.get_eq_getElem, List.getElem_append_left h] using hg ⟨k, h⟩
  · have hk : k.val - gs.length < hs.length := by simpa using (show k.val - gs.length < hs.length by have := k.isLt; simp only [List.length_append] at this; omega)
    simpa [List.get_eq_getElem, List.getElem_append_right (Nat.le_of_not_gt h),
      show N + gs.length + (k.val - gs.length) = N + k.val by omega] using hh ⟨k.val - gs.length, hk⟩

lemma compile_spec {ι κ : Type} (p : Program ι κ) (N : ℕ) (env : ι → ℕ)
    (he : ∀ i, env i < N) :
    let z := p.compile N env
    z.1.length = p.cost ∧ Good N z.1 ∧ (∀ i, z.2 i < N + z.1.length) ∧
    ∀ xs : List Bool, xs.length = N → ∀ i,
      (values xs z.1).getD (z.2 i) false = p.value (fun j => xs.getD (env j) false) i := by
  induction p generalizing N with
  | wire f => simp [Program.compile, Program.cost, Good, values, Program.value, he]
  | gate op a b =>
    refine ⟨rfl, ?_, ?_, ?_⟩
    · change Good N [⟨op, env a, env b⟩]
      intro k
      have hk : k.val = 0 := by have h := k.isLt; change k.val < 1 at h; omega
      simpa [List.get_eq_getElem, hk] using And.intro (he a) (Or.inr (he b) : op = BoolOp.not ∨ env b < N)
    · intro i; simp [Program.compile]
    · intro xs hx i
      simp [Program.compile, values, Program.value, BoolGate.value, opValue, hx,
        List.getD_eq_getElem?_getD]
      cases op <;> simp
  | @pair ι κ τ p q ihp ihq =>
    obtain ⟨hp, hgp, hop, hvp⟩ := ihp N env he
    obtain ⟨hq, hgq, hoq, hvq⟩ := ihq (N + (p.compile N env).1.length) env (fun i => by have := he i; omega)
    refine ⟨by simp only [Program.compile, Program.cost, List.length_append]; rw [hq, hp], good_append hgp hgq, ?_, ?_⟩
    · intro i; cases i with
      | inl i => simpa [Program.compile, Nat.add_assoc] using (Nat.lt_add_right (q.compile (N + (p.compile N env).1.length) env).1.length (hop i))
      | inr i => simpa [Program.compile, Nat.add_assoc] using hoq i
    · intro xs hx i
      cases i with
      | inl i =>
        change (values xs ((p.compile N env).1 ++ (q.compile (N + (p.compile N env).1.length) env).1)).getD _ false = _
        simp only [values, List.foldl_append]
        change (values (values xs (p.compile N env).1) _).getD _ false = _
        rw [values_prefix _ _ (by rw [values_length, hx]; exact hop i)]
        exact hvp xs hx i
      | inr i =>
        change (values xs ((p.compile N env).1 ++ (q.compile (N + (p.compile N env).1.length) env).1)).getD _ false = _
        simp only [values, List.foldl_append]
        change (values (values xs (p.compile N env).1) _).getD _ false = _
        simp only [Program.compile, Program.value, Sum.elim_inr]
        rw [hvq _ (by rw [values_length, hx])]
        congr 1
        funext j; exact values_prefix xs _ (hx ▸ he j)
  | @comp ι κ τ p q ihp ihq =>
    obtain ⟨hp, hgp, hop, hvp⟩ := ihp N env he
    obtain ⟨hq, hgq, hoq, hvq⟩ := ihq (N + (p.compile N env).1.length) (p.compile N env).2 hop
    refine ⟨by simp only [Program.compile, Program.cost, List.length_append]; rw [hq, hp], good_append hgp hgq,
      by simpa [Program.compile, Nat.add_assoc] using hoq, ?_⟩
    intro xs hx i
    change (values xs ((p.compile N env).1 ++ (q.compile (N + (p.compile N env).1.length) (p.compile N env).2).1)).getD _ false = _
    simp only [values, List.foldl_append]
    change (values (values xs (p.compile N env).1) _).getD _ false = _
    simp only [Program.compile, Program.value]
    rw [hvq _ (by rw [values_length, hx])]
    congr 1
    funext j; exact hvp xs hx j

def HasProgram {ι κ : Type} (f : (ι → Bool) → κ → Bool) (s : ℕ) : Prop :=
  ∃ p : Program ι κ, p.value = f ∧ p.cost ≤ s

lemma hp_wire {ι κ : Type} (f : κ → ι) : HasProgram (fun x => x ∘ f) 0 :=
  ⟨.wire f, rfl, le_rfl⟩

lemma hp_comp {ι κ τ : Type} {f : (ι → Bool) → κ → Bool} {g : (κ → Bool) → τ → Bool}
    {a b : ℕ} (hf : HasProgram f a) (hg : HasProgram g b) : HasProgram (fun x => g (f x)) (a+b) := by
  obtain ⟨p, rfl, hp⟩ := hf; obtain ⟨q, rfl, hq⟩ := hg
  exact ⟨.comp p q, rfl, Nat.add_le_add hp hq⟩

lemma hp_pair {ι κ τ : Type} {f : (ι → Bool) → κ → Bool} {g : (ι → Bool) → τ → Bool}
    {a b : ℕ} (hf : HasProgram f a) (hg : HasProgram g b) :
    HasProgram (fun x => Sum.elim (f x) (g x)) (a+b) := by
  obtain ⟨p, rfl, hp⟩ := hf; obtain ⟨q, rfl, hq⟩ := hg
  exact ⟨.pair p q, rfl, Nat.add_le_add hp hq⟩

lemma hp_mono {ι κ : Type} {f : (ι → Bool) → κ → Bool} {a b : ℕ}
    (hf : HasProgram f a) (h : a ≤ b) : HasProgram f b := by
  obtain ⟨p, hp, hc⟩ := hf; exact ⟨p, hp, hc.trans h⟩

lemma hp_map {ι κ τ : Type} {f : (ι → Bool) → κ → Bool} {a : ℕ}
    (hf : HasProgram f a) (g : τ → κ) : HasProgram (fun x => f x ∘ g) a := by
  simpa using hp_comp hf (hp_wire g)

lemma hp_op {ι : Type} (op : BoolOp) (a b : ι) :
    HasProgram (fun x (_ : Unit) => opValue op (x a) (x b)) 1 :=
  ⟨.gate op a b, rfl, le_rfl⟩

lemma hp_scalar_op {ι : Type} {f g : (ι → Bool) → Unit → Bool} {a b : ℕ}
    (hf : HasProgram f a) (hg : HasProgram g b) (op : BoolOp) :
    HasProgram (fun x (_ : Unit) => opValue op (f x ()) (g x ())) (a+b+1) := by
  exact hp_comp (hp_pair hf hg) (hp_op op (Sum.inl ()) (Sum.inr ()))

lemma hp_neg {ι : Type} {f : (ι → Bool) → Unit → Bool} {a : ℕ}
    (hf : HasProgram f a) : HasProgram (fun x (_ : Unit) => !(f x ())) (a+1) := by
  exact hp_comp hf (hp_op .not () ())

lemma hp_mul {ι : Type} {f g : (ι → Bool) → Unit → Bool} {a b : ℕ}
    (hf : HasProgram f a) (hg : HasProgram g b) :
    HasProgram (fun x (_ : Unit) => f x () * g x ()) (a+b+1) :=
  hp_scalar_op hf hg .and

lemma hp_xor_wires {ι : Type} (a b : ι) :
    HasProgram (fun x (_ : Unit) => x a + x b) 4 := by
  have ho := hp_op (ι := ι) .or a b
  have ha := hp_op (ι := ι) .and a b
  have h := hp_mul ho (hp_neg ha)
  convert h using 1
  funext x u; cases x a <;> cases x b <;> rfl

lemma hp_add {ι : Type} {f g : (ι → Bool) → Unit → Bool} {a b : ℕ}
    (hf : HasProgram f a) (hg : HasProgram g b) :
    HasProgram (fun x (_ : Unit) => f x () + g x ()) (a+b+4) :=
  hp_comp (hp_pair hf hg) (hp_xor_wires (Sum.inl ()) (Sum.inr ()))

lemma hp_const {ι : Type} (i : ι) (b : Bool) :
    HasProgram (fun _ : ι → Bool => fun _ : Unit => b) 3 := by
  have hx := hp_wire (fun _ : Unit => i)
  have hn := hp_neg hx
  cases b with
  | false =>
    have h := hp_mono (hp_mul hx hn) (by decide : 0+(0+1)+1 ≤ 3)
    convert h using 1
    funext x u; dsimp [opValue]; cases x i <;> rfl
  | true =>
    have h := hp_mono (hp_scalar_op hx hn .or) (by decide : 0+(0+1)+1 ≤ 3)
    convert h using 1
    funext x u; dsimp [opValue]; cases x i <;> rfl

lemma hp_all {ι : Type} {n s : ℕ} (f : (ι → Bool) → Fin n → Bool)
    (h : ∀ j, HasProgram (fun x (_ : Unit) => f x j) s) : HasProgram f (n*s) := by
  induction n with
  | zero => exact ⟨.wire Fin.elim0, by funext x j; exact j.elim0, Nat.zero_le _⟩
  | succ n ih =>
    have ht := ih (fun x j => f x j.succ) (fun j => h j.succ)
    have hp := hp_pair (h 0) ht
    have hm := hp_map hp (Fin.cases (Sum.inl ()) Sum.inr)
    convert hp_mono hm (by nlinarith : s+n*s ≤ (n+1)*s) using 1
    funext x j; refine Fin.cases ?_ (fun j => ?_) j <;> rfl

lemma hp_all_finite {ι κ : Type} [Fintype κ] {s : ℕ}
    (f : (ι → Bool) → κ → Bool) (h : ∀ j, HasProgram (fun x (_ : Unit) => f x j) s) :
    HasProgram f (Fintype.card κ*s) := by
  have ht := hp_all (fun x j => f x ((Fintype.equivFin κ).symm j)) (fun j => h _)
  convert hp_map ht (Fintype.equivFin κ) using 1
  funext x j; simp

lemma hp_sum {ι : Type} (i : ι) {n s : ℕ}
    (f : (ι → Bool) → Fin n → Bool)
    (h : ∀ j, HasProgram (fun x (_ : Unit) => f x j) s) :
    HasProgram (fun x (_ : Unit) => ∑ j, f x j) (n*(s+4)+3) := by
  induction n with
  | zero => simpa using hp_const i false
  | succ n ih =>
    have ht := ih (fun x j => f x j.succ) (fun j => h j.succ)
    have hp := hp_add (h 0) ht
    convert hp_mono hp (by nlinarith : s+(n*(s+4)+3)+4 ≤ (n+1)*(s+4)+3) using 1
    funext x u; simp [Fin.sum_univ_succ]

lemma hp_prod {ι : Type} (i : ι) {n s : ℕ}
    (f : (ι → Bool) → Fin n → Bool)
    (h : ∀ j, HasProgram (fun x (_ : Unit) => f x j) s) :
    HasProgram (fun x (_ : Unit) => ∏ j, f x j) (n*(s+1)+3) := by
  induction n with
  | zero => simpa using hp_const i true
  | succ n ih =>
    have ht := ih (fun x j => f x j.succ) (fun j => h j.succ)
    have hp := hp_mul (h 0) ht
    convert hp_mono hp (by nlinarith : s+(n*(s+1)+3)+1 ≤ (n+1)*(s+1)+3) using 1
    funext x u; simp [Fin.prod_univ_succ]

lemma program_circuit {N M s : ℕ} {f : (Fin N → Bool) → Fin M → Bool}
    (hf : HasProgram f s) :
    ∃ G : BoolCircuit N M, G.WellFormed ∧ G.size ≤ s ∧ G.eval = f := by
  obtain ⟨p, hp, hc⟩ := hf
  let z := p.compile N Fin.val
  obtain ⟨hz, hg, ho, hv⟩ := compile_spec p N Fin.val (fun i => i.isLt)
  refine ⟨⟨z.1, z.2⟩, ⟨hg, ho⟩, ?_, ?_⟩
  · change z.1.length ≤ s; exact hz.trans_le hc
  · funext x j
    change (values (List.ofFn x) z.1).getD (z.2 j) false = f x j
    rw [hv _ (by simp)]
    have hx : (fun i : Fin N => (List.ofFn x).getD i.val false) = x := by
      funext i; simp [i.isLt]
    rw [hx, hp]

end RandomDimReduction.Channel.BooleanPrograms
end
end p2mFlat_Solutions_BooleanPrograms
attribute [-simp] RandomDimReduction.Channel.BooleanPrograms.bool_false RandomDimReduction.Channel.BooleanPrograms.bool_true


