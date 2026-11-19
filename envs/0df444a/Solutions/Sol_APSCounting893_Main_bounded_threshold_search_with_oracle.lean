-- Prove2me | solution 1 for APSCounting893.Main.bounded_threshold_search_with_oracle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T17:41:18.907248+00:00
-- url     : https://prove2.me/submissions/c9aaf530-c912-4157-b636-daa8eb24d045

import Definitions.Def_APSCounting893_Main_CoefficientLanguages
import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
import Theorems.Thm_APSCounting893_Main_stack_function_polynomial_simulation
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma unaryPrefix_append_injective (a b : ℕ) (u v : Word)
    (h : List.replicate a true ++ false :: u = List.replicate b true ++ false :: v) :
    a = b ∧ u = v := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => simpa using h
      | succ b => simp [List.replicate_succ] at h
  | succ a ih =>
      cases b with
      | zero => simp [List.replicate_succ] at h
      | succ b =>
          simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨hab, huv⟩ := ih b h
          exact ⟨congrArg Nat.succ hab, huv⟩

lemma nat_bits_fold (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih => simp only [Nat.bits_append_bit n b hn, List.foldr_cons, ih]

lemma encodeNat_append_injective (a b : ℕ) (u v : Word)
    (h : encodeNat a ++ u = encodeNat b ++ v) : a = b ∧ u = v := by
  have hh : List.replicate a.bits.length true ++ false :: (a.bits ++ u) =
      List.replicate b.bits.length true ++ false :: (b.bits ++ v) := by
    simpa only [encodeNat, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using h
  obtain ⟨hlen, hsuffix⟩ := unaryPrefix_append_injective _ _ _ _ hh
  have hbits : a.bits = b.bits := by
    have ht := congrArg (List.take a.bits.length) hsuffix
    rw [List.take_left] at ht
    rwa [hlen, List.take_left] at ht
  have hab : a = b := by
    have ht := congrArg (List.foldr Nat.bit 0) hbits
    simpa only [nat_bits_fold] using ht
  subst b
  exact ⟨rfl, List.append_cancel_left hsuffix⟩

lemma encodeNatList_append_injective (l l' : List ℕ) (u v : Word)
    (h : encodeList encodeNat l ++ u = encodeList encodeNat l' ++ v) : l = l' ∧ u = v := by
  have hh : encodeNat l.length ++ (l.flatMap encodeNat ++ u) =
      encodeNat l'.length ++ (l'.flatMap encodeNat ++ v) := by simpa only [encodeList, List.append_assoc] using h
  obtain ⟨hlen, hsuffix⟩ := encodeNat_append_injective _ _ _ _ hh
  clear h hh
  induction l generalizing l' with
  | nil =>
      have hl' : l' = [] := List.length_eq_zero_iff.mp hlen.symm
      subst l'
      exact ⟨rfl, hsuffix⟩
  | cons a l ih =>
      cases l' with
      | nil => simp at hlen
      | cons b l' =>
          have hh : encodeNat a ++ (l.flatMap encodeNat ++ u) =
              encodeNat b ++ (l'.flatMap encodeNat ++ v) := by
            simpa only [List.flatMap_cons, List.append_assoc] using hsuffix
          obtain ⟨hab, hs⟩ := encodeNat_append_injective _ _ _ _ hh
          obtain ⟨hll, huv⟩ := ih l' (Nat.succ.inj hlen) hs
          exact ⟨congrArg₂ List.cons hab hll, huv⟩

lemma coefficientPart_append_injective (p p' : CoefficientPart) (u v : Word)
    (h : p.encode ++ u = p'.encode ++ v) : p = p' ∧ u = v := by
  cases p <;> cases p' <;> simp_all [CoefficientPart.encode]

lemma coefficientQuery_injective {k : ℕ}
    (x x' : Word) (e e' : Fin (k + 1) →₀ ℕ) (part part' : CoefficientPart) (q q' : ℕ)
    (h : coefficientQuery x e part q = coefficientQuery x' e' part' q') :
    x = x' ∧ e = e' ∧ part = part' ∧ q = q' := by
  have hh := encodeNat_append_injective x.length x'.length
    (x ++ encodeList encodeNat (List.ofFn (fun i => e i)) ++ part.encode ++ encodeNat q)
    (x' ++ encodeList encodeNat (List.ofFn (fun i => e' i)) ++ part'.encode ++ encodeNat q')
    (by simpa only [coefficientQuery, List.append_assoc] using h)
  have hx : x = x' := by
    have ht := congrArg (List.take x.length) hh.2
    simp only [List.append_assoc] at ht
    rw [List.take_left] at ht
    rwa [hh.1, List.take_left] at ht
  subst x'
  have hs := List.append_cancel_left (show
    x ++ (encodeList encodeNat (List.ofFn (fun i => e i)) ++ part.encode ++ encodeNat q) =
    x ++ (encodeList encodeNat (List.ofFn (fun i => e' i)) ++ part'.encode ++ encodeNat q') from
      by simpa only [List.append_assoc] using hh.2)
  obtain ⟨helist, hs⟩ := encodeNatList_append_injective _ _
    (part.encode ++ encodeNat q) (part'.encode ++ encodeNat q')
    (by simpa only [List.append_assoc] using hs)
  have he : e = e' := by
    apply Finsupp.ext
    intro i
    exact congrFun (List.ofFn_injective helist) i
  obtain ⟨hpart, hq⟩ := coefficientPart_append_injective _ _ _ _ hs
  have hq' : q = q' := (encodeNat_append_injective q q' [] [] (by simpa using hq)).1
  exact ⟨rfl, he, hpart, hq'⟩

lemma coefficientBitLanguage_query_iff {k : ℕ} (rho : CoefficientRepresentation k)
    (x : Word) (e : Fin (k + 1) →₀ ℕ) (part : CoefficientPart) (q : ℕ) :
    CoefficientBitLanguage rho (coefficientQuery x e part q) ↔ representationBit (rho x e) part q = true := by
  constructor
  · rintro ⟨x', e', part', q', h, hb⟩
    obtain ⟨hx, he, hp, hq⟩ := coefficientQuery_injective _ _ _ _ _ _ _ _ h
    subst x'; subst e'; subst part'; subst q'
    exact hb
  · intro h
    exact ⟨x, e, part, q, rfl, h⟩

end APSCounting893.Main
end Component_0

section Component_1

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main

def incrementBits : Word → Word
  | [] => [true]
  | false :: w => true :: w
  | true :: w => false :: incrementBits w

lemma incrementBits_length_le (w : Word) : (incrementBits w).length ≤ w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [incrementBits] <;> omega

lemma incrementBits_nat_bits (n : ℕ) : incrementBits n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
      cases b with
      | false =>
          rw [Nat.bits_append_bit n false hn]
          have heq : Nat.bit false n + 1 = Nat.bit true n := by simp [Nat.bit_val]
          rw [heq, Nat.bits_append_bit n true (by intro; rfl)]
          rfl
      | true =>
          rw [Nat.bits_append_bit n true hn]
          change false :: incrementBits n.bits = _
          rw [ih]
          have heq : Nat.bit true n + 1 = Nat.bit false (n + 1) := by simp [Nat.bit_val]; omega
          rw [heq, Nat.bits_append_bit (n + 1) false (by intro h; omega)]

lemma incrementBits_ne_nil (w : Word) : incrementBits w ≠ [] := by
  cases w with
  | nil => decide
  | cons b w => cases b <;> simp [incrementBits]

lemma canonicalBits_tail (b : Bool) (w : Word) (h : canonicalBits (b :: w) = true) :
    canonicalBits w = true := by
  cases w <;> simpa [canonicalBits] using h

lemma bitsValue_pos_of_canonical {w : Word} (h : canonicalBits w = true) (hne : w ≠ []) :
    0 < bitsValue w := by
  induction w with
  | nil => exact (hne rfl).elim
  | cons b w ih =>
      cases w with
      | nil =>
          have hb : b = true := h
          subst b
          decide
      | cons c w =>
          have ht : 0 < bitsValue (c :: w) := ih (canonicalBits_tail b _ h) (by simp)
          cases b <;> simp only [bitsValue, List.foldr_cons, Nat.bit_val] at ht ⊢ <;> omega

lemma bitsValue_bits_of_canonical (w : Word) (h : canonicalBits w = true) :
    (bitsValue w).bits = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      have hw := canonicalBits_tail b w h
      change (Nat.bit b (bitsValue w)).bits = b :: w
      rw [Nat.bits_append_bit (bitsValue w) b]
      · rw [ih hw]
      · intro hn
        by_cases hz : w = []
        · subst w
          exact h
        · exact ((bitsValue_pos_of_canonical hw hz).ne' hn).elim

lemma canonicalBits_nat_bits (n : ℕ) : canonicalBits n.bits = true := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      by_cases hz : n = 0
      · subst n
        exact hn rfl
      · have hnil : n.bits ≠ [] := by
          intro heq
          have hv := nat_bits_fold n
          rw [heq] at hv
          exact hz hv.symm
        cases hw : n.bits with
        | nil => exact (hnil hw).elim
        | cons c w => simpa [canonicalBits, hw] using ih

lemma canonicalBits_append_singleton (w : Word) (b : Bool) : canonicalBits (w ++ [b]) = b := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      cases w with
      | nil => rfl
      | cons c w => exact ih

lemma canonicalBits_eq_reverse_headD (w : Word) : canonicalBits w = w.reverse.headD true := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w b ih => simp [canonicalBits_append_singleton]

lemma nat_bits_reverse_head (n : ℕ) : n.bits.reverse.headD true = true := by
  rw [← canonicalBits_eq_reverse_headD, canonicalBits_nat_bits]

end APSCounting893.Main
end Component_1

section Component_2
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace APSCounting893.Main

def additionBit (a b c : Bool) : Bool := xor (xor a b) c
def additionCarry (a b c : Bool) : Bool := (a && b)||(a && c)||(b && c)

lemma addition_bits_identity (a b c : Bool) :
    a.toNat+b.toNat+c.toNat=(additionBit a b c).toNat+2*(additionCarry a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

def binaryAddAux : Word → Word → Bool → Word
  | [],[],c => if c then [true] else []
  | a::xs,[],c => additionBit a false c::binaryAddAux xs [] (additionCarry a false c)
  | [],b::ys,c => additionBit false b c::binaryAddAux [] ys (additionCarry false b c)
  | a::xs,b::ys,c => additionBit a b c::binaryAddAux xs ys (additionCarry a b c)
termination_by xs ys _ => xs.length+ys.length

lemma bitsValue_cons_addition (b : Bool) (w : Word) : bitsValue (b::w)=2*bitsValue w+b.toNat := by
  simp only [bitsValue,List.foldr_cons,Nat.bit_val]

lemma bitsValue_nil_addition : bitsValue ([] : Word)=0 := rfl

lemma binaryAddAux_value (xs ys : Word) (c : Bool) :
    bitsValue (binaryAddAux xs ys c)=bitsValue xs+bitsValue ys+c.toNat := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [binaryAddAux,bitsValue]
    | cons b ys ih =>
      simp only [binaryAddAux,bitsValue_cons_addition,bitsValue_nil_addition]
      rw [ih]
      have hh:=addition_bits_identity false b c
      simp only [Bool.toNat_false,zero_add,bitsValue_nil_addition] at *
      omega
  | cons a xs ih =>
    cases ys with
    | nil =>
      simp only [binaryAddAux,bitsValue_cons_addition,bitsValue_nil_addition]
      rw [ih]
      have hh:=addition_bits_identity a false c
      simp only [Bool.toNat_false,add_zero,bitsValue_nil_addition] at *
      omega
    | cons b ys =>
      simp only [binaryAddAux,bitsValue_cons_addition]
      rw [ih]
      have hh:=addition_bits_identity a b c
      omega

lemma binaryAddAux_length (xs ys : Word) (c : Bool) :
    (binaryAddAux xs ys c).length ≤ max xs.length ys.length+1 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [binaryAddAux,bitsValue]
    | cons b ys ih =>
      simp only [binaryAddAux,List.length_cons,List.length_nil,Nat.zero_max] at ih ⊢
      exact Nat.succ_le_succ (ih _)
  | cons a xs ih =>
    cases ys with
    | nil =>
      simp only [binaryAddAux,List.length_cons,List.length_nil,Nat.max_zero]
      have hh:=ih [] (additionCarry a false c)
      simp only [List.length_nil,Nat.max_zero] at hh
      omega
    | cons b ys =>
      simp only [binaryAddAux,List.length_cons]
      have hh:=ih ys (additionCarry a b c)
      omega

end APSCounting893.Main
end Component_2

section Component_3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

inductive ArithmeticWordOp (Q : Type) (r : ℕ) where
  | escape (src dst : Fin (r+2)) (next : Q)
  | add (left right dst : Fin (r+2)) (next : Q)
  | pop (reg : Fin (r+2)) (zero one empty : Q)
  | jump (next : Q)
  | push (dst : Fin (r + 2)) (b : Bool) (next : Q)
  | clear (reg : Fin (r + 2)) (next : Q)
  | reverse (src dst : Fin (r + 2)) (next : Q)
  | copy (src dst tmp scratch : Fin (r + 2)) (next : Q)
  | pair (src dst : Fin (r + 2)) (next : Q) (failure : Bool)
  | nat (src counter dst : Fin (r + 2)) (next : Q) (failure : Bool)
  | length (src counter tmp : Fin (r + 2)) (next : Q)
  | encodeNat (first second dst : Fin (r + 2)) (next : Q)
  | prepend (dst : Fin (r + 2)) (word : Word) (next : Q)
  | check (src : Fin (r + 2)) (word : Word) (next : Q) (failure : Bool)
  | compareLength (left right : Fin (r + 2)) (less equal greater : Q)
  | compareLex (left right : Fin (r + 2)) (less equal greater : Q)
  | query (reg : Fin (r + 2)) (yes no : Q)
  | halt (b : Bool)

def ArithmeticWordOp.constantLength {Q : Type} {r : ℕ} : ArithmeticWordOp Q r → ℕ
  | .prepend _ word _ => word.length
  | .check _ word _ _ => word.length
  | _ => 0

noncomputable def arithmeticAssemblyConstantBound {Q : Type} [Fintype Q] {r : ℕ} (table : Q → ArithmeticWordOp Q r) : ℕ :=
  ∑ q, (table q).constantLength

inductive ArithmeticAssemblyPhase (D : ℕ) where
  | entry | p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10
  | addLoop (c : Bool) | addEmpty (c : Bool)
  | addRead (c a : Bool) | addEmit (c a b : Bool) | addFinish
  | constant (i : Fin (D + 1))
  deriving DecidableEq, Fintype

inductive ArithmeticAssemblyControl (Q : Type) (D : ℕ) where
  | at (site : Q) (phase : ArithmeticAssemblyPhase D)
  | halt (b : Bool)
  deriving DecidableEq, Fintype

open ArithmeticAssemblyControl ArithmeticAssemblyPhase in
noncomputable def arithmeticAssemble {Q : Type} [Fintype Q] {r : ℕ} (table : Q → ArithmeticWordOp Q r) (initial : Q) :
    StackProgram (ArithmeticAssemblyControl Q (arithmeticAssemblyConstantBound table)) r where
  initial := .at initial .entry
  transition := fun control => match control with
    | .halt b => .halt b
    | .at q phase =>
      let go := fun next => ArithmeticAssemblyControl.at next ArithmeticAssemblyPhase.entry
      let here := fun phase => ArithmeticAssemblyControl.at q phase
      match table q with
      | .escape src dst next => match phase with
        | .entry => .pop src (here .p1) (here .p2) (go next)
        | .p1 => .push dst false (here .p3)
        | .p2 => .push dst true (here .p3)
        | .p3 => .push dst true (here .entry)
        | _ => .halt false
      | .add left right dst next => match phase with
        | .entry => .jump (here (.addLoop false))
        | .addLoop c => .pop left (here (.addRead c false)) (here (.addRead c true)) (here (.addEmpty c))
        | .addRead c a => .pop right (here (.addEmit c a false)) (here (.addEmit c a true)) (here (.addEmit c a false))
        | .addEmpty c => .pop right (here (.addEmit c false false)) (here (.addEmit c false true))
            (if c then here .addFinish else go next)
        | .addEmit c a b => .push dst (additionBit a b c) (here (.addLoop (additionCarry a b c)))
        | .addFinish => .push dst true (go next)
        | _ => .halt false
      | .pop reg zero one empty => .pop reg (go zero) (go one) (go empty)
      | .jump next => .jump (go next)
      | .push dst b next => .push dst b (go next)
      | .clear reg next => .pop reg (here .entry) (here .entry) (go next)
      | .reverse src dst next => match phase with
        | .entry => .pop src (here .p1) (here .p2) (go next)
        | .p1 => .push dst false (here .entry)
        | .p2 => .push dst true (here .entry)
        | _ => .halt false
      | .copy src dst tmp scratch next => match phase with
        | .entry => .pop src (here .p1) (here .p2) (here .p5)
        | .p1 => .push scratch false (here .p3)
        | .p2 => .push scratch true (here .p4)
        | .p3 => .push tmp false (here .entry)
        | .p4 => .push tmp true (here .entry)
        | .p5 => .pop tmp (here .p6) (here .p7) (here .p8)
        | .p6 => .push src false (here .p5)
        | .p7 => .push src true (here .p5)
        | .p8 => .pop scratch (here .p9) (here .p10) (go next)
        | .p9 => .push dst false (here .p8)
        | .p10 => .push dst true (here .p8)
        | _ => .halt false
      | .pair src dst next failure => match phase with
        | .entry => .pop src (go next) (here .p1) (.halt failure)
        | .p1 => .pop src (here .p2) (here .p3) (.halt failure)
        | .p2 => .push dst false (here .entry)
        | .p3 => .push dst true (here .entry)
        | _ => .halt false
      | .nat src counter dst next failure => match phase with
        | .entry => .pop src (here .p2) (here .p1) (.halt failure)
        | .p1 => .push counter true (here .entry)
        | .p2 => .pop counter (here .p3) (here .p3) (here .p6)
        | .p3 => .pop src (here .p4) (here .p5) (.halt failure)
        | .p4 => .push dst false (here .p2)
        | .p5 => .push dst true (here .p2)
        | .p6 => .peek dst (.halt failure) (go next) (go next)
        | _ => .halt false
      | .length src counter tmp next => match phase with
        | .entry => .pop src (here .p1) (here .p1) (go next)
        | .p1 => .pop counter (here .p2) (here .p3) (here .p2)
        | .p2 => .push counter true (here .p4)
        | .p3 => .push tmp false (here .p1)
        | .p4 => .pop tmp (here .p5) (here .p6) (here .entry)
        | .p5 => .push counter false (here .p4)
        | .p6 => .push counter true (here .p4)
        | _ => .halt false
      | .encodeNat first second dst next => match phase with
        | .entry => .pop first (here .p1) (here .p2) (here .p3)
        | .p1 => .push dst false (here .entry)
        | .p2 => .push dst true (here .entry)
        | .p3 => .push dst false (here .p4)
        | .p4 => .pop second (here .p5) (here .p5) (go next)
        | .p5 => .push dst true (here .p4)
        | _ => .halt false
      | .prepend dst word next => match phase with
        | .entry => .jump (here (.constant 0))
        | .constant i => if h : i.val < word.length then
            .push dst (word.reverse[i.val]'(by simpa using h))
              (here (.constant (Fin.ofNat _ (i.val + 1))))
            else .jump (go next)
        | _ => .halt false
      | .check src word next failure => match phase with
        | .entry => .jump (here (.constant 0))
        | .constant i => if h : i.val < word.length then
            let target := here (.constant (Fin.ofNat _ (i.val + 1)))
            .pop src (if word[i.val] then .halt failure else target)
              (if word[i.val] then target else .halt failure) (.halt failure)
            else .jump (go next)
        | _ => .halt false
      | .compareLength left right less equal greater => match phase with
        | .entry => .pop left (here .p1) (here .p1) (here .p2)
        | .p1 => .pop right (here .entry) (here .entry) (go greater)
        | .p2 => .pop right (go less) (go less) (go equal)
        | _ => .halt false
      | .compareLex left right less equal greater => match phase with
        | .entry => .pop left (here .p1) (here .p2) (here .p3)
        | .p1 => .pop right (here .entry) (go less) (go greater)
        | .p2 => .pop right (go greater) (here .entry) (go greater)
        | .p3 => .pop right (go less) (go less) (go equal)
        | _ => .halt false
      | .query reg yes no => .query reg (go yes) (go no)
      | .halt b => .halt b

end APSCounting893.Main
end Component_3

section Component_4
set_option autoImplicit false
namespace APSCounting893.Main

end APSCounting893.Main
end Component_4

section Component_5

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_reverse_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src dst : Fin (r + 2)) (hne : src ≠ dst) (loop zero one finish : Q)
    (hloop : P.transition loop = .pop src zero one finish)
    (hzero : P.transition zero = .push dst false loop)
    (hone : P.transition one = .push dst true loop)
    (cfg : StackConfig Q r) (hs : cfg.state = loop) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) :
    P.exec A cfg (2 * w.length + 1) =
      { state := finish,
        regs := Function.update (Function.update cfg.regs src []) dst (w.reverse ++ cfg.regs dst),
        answer := none } := by
  classical
  induction w generalizing cfg with
  | nil =>
      change P.step A cfg = _
      have hup : Function.update cfg.regs src [] = cfg.regs := by
        rw [← hw]
        exact Function.update_eq_self src cfg.regs
      simp [StackProgram.step, hs, ha, hloop, hw, hup]
  | cons b w ih =>
      let next := if b then one else zero
      let cfg1 : StackConfig Q r :=
        { state := next, regs := Function.update cfg.regs src w, answer := none }
      let cfg2 : StackConfig Q r :=
        { state := loop, regs := Function.update (Function.update cfg.regs src w) dst (b :: cfg.regs dst), answer := none }
      have hstep1 : P.step A cfg = cfg1 := by
        cases b <;> simp [StackProgram.step, hs, ha, hloop, hw, cfg1, next]
      have hstep2 : P.step A cfg1 = cfg2 := by
        cases b <;> simp [StackProgram.step, cfg1, cfg2, next, hzero, hone, Ne.symm hne]
      have hsrc : cfg2.regs src = w := by simp [cfg2, hne]
      have hrec := ih cfg2 rfl rfl hsrc
      have htime : 2 * (b :: w).length + 1 = 1 + (1 + (2 * w.length + 1)) := by simp; omega
      rw [htime, StackProgram.exec_add, StackProgram.exec_one, hstep1,
        StackProgram.exec_add, StackProgram.exec_one, hstep2, hrec]
      congr 1
      funext j
      by_cases hjs : j = src
      · subst j
        simp [cfg2, Function.update, hne, Ne.symm hne]
      · by_cases hjd : j = dst
        · subst j
          simp [cfg2, Function.update, hne, Ne.symm hne, List.reverse_cons, List.append_assoc]
        · simp [cfg2, Function.update, hjs, hjd]

lemma stack_map_reverse_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (f : Bool → Bool) (src dst : Fin (r + 2)) (hne : src ≠ dst) (loop zero one finish : Q)
    (hloop : P.transition loop = .pop src zero one finish)
    (hzero : P.transition zero = .push dst (f false) loop)
    (hone : P.transition one = .push dst (f true) loop)
    (cfg : StackConfig Q r) (hs : cfg.state = loop) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) :
    P.exec A cfg (2 * w.length + 1) =
      { state := finish,
        regs := Function.update (Function.update cfg.regs src []) dst ((w.map f).reverse ++ cfg.regs dst),
        answer := none } := by
  classical
  induction w generalizing cfg with
  | nil =>
      change P.step A cfg = _
      have hup : Function.update cfg.regs src [] = cfg.regs := by
        rw [← hw]
        exact Function.update_eq_self src cfg.regs
      simp [StackProgram.step, hs, ha, hloop, hw, hup]
  | cons b w ih =>
      let next := if b then one else zero
      let cfg1 : StackConfig Q r :=
        { state := next, regs := Function.update cfg.regs src w, answer := none }
      let cfg2 : StackConfig Q r :=
        { state := loop, regs := Function.update (Function.update cfg.regs src w) dst (f b :: cfg.regs dst), answer := none }
      have hstep1 : P.step A cfg = cfg1 := by
        cases b <;> simp [StackProgram.step, hs, ha, hloop, hw, cfg1, next]
      have hstep2 : P.step A cfg1 = cfg2 := by
        cases b <;> simp [StackProgram.step, cfg1, cfg2, next, hzero, hone, Ne.symm hne]
      have hsrc : cfg2.regs src = w := by simp [cfg2, hne]
      have hrec := ih cfg2 rfl rfl hsrc
      have htime : 2 * (b :: w).length + 1 = 1 + (1 + (2 * w.length + 1)) := by simp; omega
      rw [htime, StackProgram.exec_add, StackProgram.exec_one, hstep1,
        StackProgram.exec_add, StackProgram.exec_one, hstep2, hrec]
      congr 1
      funext j
      by_cases hjs : j = src
      · subst j
        simp [cfg2, Function.update, hne, Ne.symm hne]
      · by_cases hjd : j = dst
        · subst j
          simp [cfg2, Function.update, hne, Ne.symm hne, List.map_cons, List.reverse_cons, List.append_assoc]
        · simp [cfg2, Function.update, hjs, hjd]

end APSCounting893.Main
end Component_5

section Component_6
set_option autoImplicit false
namespace APSCounting893.Main
lemma pairWord_length (x y : Word) : (pairWord x y).length = 2 * x.length + 1 + y.length := by
  simp [pairWord, List.length_flatMap, List.sum_replicate, Nat.mul_comm, Nat.add_assoc, Nat.add_comm]


end APSCounting893.Main
end Component_6

section Component_7
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_escaped_prefix_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src dst : Fin (r+2)) (hne : src ≠ dst) (loop zero one flag finish : Q)
    (hloop : P.transition loop=.pop src zero one finish)
    (hzero : P.transition zero=.push dst false flag)
    (hone : P.transition one=.push dst true flag)
    (hflag : P.transition flag=.push dst true loop)
    (cfg : StackConfig Q r) (hs : cfg.state=loop) (ha : cfg.answer=none)
    (w : Word) (hw : cfg.regs src=w) :
    P.exec A cfg (3*w.length+1) =
      {state := finish,regs := Function.update (Function.update cfg.regs src []) dst
        (w.reverse.flatMap (fun b => [true,b]) ++ cfg.regs dst),answer := none} := by
  classical
  induction w generalizing cfg with
  | nil =>
    change P.step A cfg=_
    have hup : Function.update cfg.regs src []=cfg.regs := by
      rw [←hw]
      exact Function.update_eq_self src cfg.regs
    simp [StackProgram.step,hs,ha,hloop,hw,hup]
  | cons b w ih =>
    let next := if b then one else zero
    let cfg1 : StackConfig Q r := {state:=next,regs:=Function.update cfg.regs src w,answer:=none}
    let cfg2 : StackConfig Q r := {state:=flag,regs:=Function.update (Function.update cfg.regs src w) dst (b::cfg.regs dst),answer:=none}
    let cfg3 : StackConfig Q r := {state:=loop,regs:=Function.update (Function.update cfg.regs src w) dst (true::b::cfg.regs dst),answer:=none}
    have h1 : P.step A cfg=cfg1 := by
      cases b <;> simp [StackProgram.step,hs,ha,hloop,hw,cfg1,next]
    have h2 : P.step A cfg1=cfg2 := by
      cases b <;> simp [StackProgram.step,cfg1,cfg2,next,hzero,hone,Ne.symm hne]
    have h3 : P.step A cfg2=cfg3 := by
      simp [StackProgram.step,cfg2,cfg3,hflag]
    have hsrc : cfg3.regs src=w := by simp [cfg3,hne]
    have hrec:=ih cfg3 rfl rfl hsrc
    have ht : 3*(b::w).length+1=1+(1+(1+(3*w.length+1))) := by simp;omega
    rw [ht,StackProgram.exec_add,StackProgram.exec_one,h1,
      StackProgram.exec_add,StackProgram.exec_one,h2,
      StackProgram.exec_add,StackProgram.exec_one,h3,hrec]
    congr 1
    funext j
    by_cases hjs : j=src
    · subst j
      simp [cfg3,Function.update,hne,Ne.symm hne]
    · by_cases hjd : j=dst
      · subst j
        simp [cfg3,Function.update,hne,Ne.symm hne,List.reverse_cons,List.flatMap_append,List.append_assoc]
      · simp [cfg3,Function.update,hjs,hjd]

end APSCounting893.Main
end Component_7

section Component_8
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_clear_word_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src : Fin (r+2)) (loop finish : Q) (hloop : P.transition loop=.pop src loop loop finish)
    (cfg : StackConfig Q r) (hs : cfg.state=loop) (ha : cfg.answer=none) (w : Word) (hw : cfg.regs src=w) :
    P.exec A cfg (w.length+1)={state:=finish,regs:=Function.update cfg.regs src [],answer:=none} := by
  classical
  induction w generalizing cfg with
  | nil => simp [StackProgram.exec_one,StackProgram.step,hs,ha,hloop,hw]
  | cons b w ih =>
    let cfg1 : StackConfig Q r:={state:=loop,regs:=Function.update cfg.regs src w,answer:=none}
    have hstep : P.step A cfg=cfg1 := by cases b <;> simp [StackProgram.step,hs,ha,hloop,hw,cfg1]
    have hrec:=ih cfg1 rfl rfl (by simp [cfg1])
    rw [show (b::w).length+1=1+(w.length+1) by simp;omega,StackProgram.exec_add,StackProgram.exec_one,hstep,hrec]
    simp [cfg1]

end APSCounting893.Main
end Component_8

section Component_9
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma arithmeticAssemble_escape {Q : Type} [Fintype Q] {r : ℕ} (table : Q → ArithmeticWordOp Q r)
    (initial q next : Q) (A : Language) (src dst : Fin (r+2)) (hne : src≠dst)
    (ht : table q=.escape src dst next)
    (cfg : StackConfig (ArithmeticAssemblyControl Q (arithmeticAssemblyConstantBound table)) r)
    (hs : cfg.state=.at q .entry) (ha : cfg.answer=none) (w : Word) (hw : cfg.regs src=w) :
    (arithmeticAssemble table initial).exec A cfg (3*w.length+1)=
      {state:=.at next .entry,regs:=Function.update (Function.update cfg.regs src []) dst
        (w.reverse.flatMap (fun b=>[true,b])++cfg.regs dst),answer:=none} := by
  exact stack_escaped_prefix_routine (arithmeticAssemble table initial) A src dst hne
    (.at q .entry) (.at q .p1) (.at q .p2) (.at q .p3) (.at next .entry)
    (by simp [arithmeticAssemble,ht]) (by simp [arithmeticAssemble,ht])
    (by simp [arithmeticAssemble,ht]) (by simp [arithmeticAssemble,ht]) cfg hs ha w hw

lemma arithmeticAssemble_clear {Q : Type} [Fintype Q] {r : ℕ} (table : Q → ArithmeticWordOp Q r)
    (initial q next : Q) (A : Language) (src : Fin (r+2)) (ht : table q=.clear src next)
    (cfg : StackConfig (ArithmeticAssemblyControl Q (arithmeticAssemblyConstantBound table)) r)
    (hs : cfg.state=.at q .entry) (ha : cfg.answer=none) (w : Word) (hw : cfg.regs src=w) :
    (arithmeticAssemble table initial).exec A cfg (w.length+1)=
      {state:=.at next .entry,regs:=Function.update cfg.regs src [],answer:=none} :=
  stack_clear_word_routine (arithmeticAssemble table initial) A src (.at q .entry) (.at next .entry)
    (by simp [arithmeticAssemble,ht]) cfg hs ha w hw

end APSCounting893.Main
end Component_9

section Component_10

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_distribute_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src dst tmp : Fin (r + 2)) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (loop zero one zero' one' finish : Q)
    (hloop : P.transition loop = .pop src zero one finish)
    (hzero : P.transition zero = .push dst false zero')
    (hone : P.transition one = .push dst true one')
    (hzero' : P.transition zero' = .push tmp false loop)
    (hone' : P.transition one' = .push tmp true loop)
    (cfg : StackConfig Q r) (hs : cfg.state = loop) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) :
    P.exec A cfg (3 * w.length + 1) =
      { state := finish,
        regs := Function.update (Function.update (Function.update cfg.regs src []) dst
          (w.reverse ++ cfg.regs dst)) tmp (w.reverse ++ cfg.regs tmp),
        answer := none } := by
  classical
  induction w generalizing cfg with
  | nil =>
      change P.step A cfg = _
      have hup : Function.update cfg.regs src [] = cfg.regs := by
        rw [← hw]
        exact Function.update_eq_self src cfg.regs
      simp [StackProgram.step, hs, ha, hloop, hw, hup]
  | cons b w ih =>
      let next := if b then one else zero
      let next' := if b then one' else zero'
      let cfg1 : StackConfig Q r :=
        { state := next, regs := Function.update cfg.regs src w, answer := none }
      let cfg2 : StackConfig Q r :=
        { state := next', regs := Function.update (Function.update cfg.regs src w) dst (b :: cfg.regs dst), answer := none }
      let cfg3 : StackConfig Q r :=
        { state := loop, regs := Function.update (Function.update (Function.update cfg.regs src w) dst
          (b :: cfg.regs dst)) tmp (b :: cfg.regs tmp), answer := none }
      have hstep1 : P.step A cfg = cfg1 := by
        cases b <;> simp [StackProgram.step, hs, ha, hloop, hw, cfg1, next]
      have hstep2 : P.step A cfg1 = cfg2 := by
        cases b <;> simp [StackProgram.step, cfg1, cfg2, next, next', hzero, hone, Ne.symm hsd]
      have hstep3 : P.step A cfg2 = cfg3 := by
        cases b <;> simp [StackProgram.step, cfg2, cfg3, next', hzero', hone', Ne.symm hst, Ne.symm hdt]
      have hsrc : cfg3.regs src = w := by simp [cfg3, hsd, hst]
      have hrec := ih cfg3 rfl rfl hsrc
      have htime : 3 * (b :: w).length + 1 = 1 + (1 + (1 + (3 * w.length + 1))) := by simp; omega
      rw [htime, StackProgram.exec_add, StackProgram.exec_one, hstep1,
        StackProgram.exec_add, StackProgram.exec_one, hstep2,
        StackProgram.exec_add, StackProgram.exec_one, hstep3, hrec]
      congr 1
      funext j
      by_cases hjs : j = src
      · subst j
        simp [cfg3, Function.update, hsd, hst, Ne.symm hsd, Ne.symm hst]
      · by_cases hjd : j = dst
        · subst j
          simp [cfg3, Function.update, hsd, hdt, Ne.symm hsd, Ne.symm hdt,
            List.reverse_cons, List.append_assoc]
        · by_cases hjt : j = tmp
          · subst j
            simp [cfg3, Function.update, hst, hdt, Ne.symm hst, Ne.symm hdt,
              List.reverse_cons, List.append_assoc]
          · simp [cfg3, Function.update, hjs, hjd, hjt]

end APSCounting893.Main
end Component_10

section Component_11

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_copy_reverse_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src dst tmp : Fin (r + 2)) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (loop zero one zero' one' restore restoreZero restoreOne finish : Q)
    (hloop : P.transition loop = .pop src zero one restore)
    (hzero : P.transition zero = .push dst false zero')
    (hone : P.transition one = .push dst true one')
    (hzero' : P.transition zero' = .push tmp false loop)
    (hone' : P.transition one' = .push tmp true loop)
    (hrestore : P.transition restore = .pop tmp restoreZero restoreOne finish)
    (hrestoreZero : P.transition restoreZero = .push src false restore)
    (hrestoreOne : P.transition restoreOne = .push src true restore)
    (cfg : StackConfig Q r) (hs : cfg.state = loop) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) (htmp : cfg.regs tmp = []) :
    P.exec A cfg (5 * w.length + 2) =
      { state := finish,
        regs := Function.update (Function.update cfg.regs dst (w.reverse ++ cfg.regs dst)) tmp [], answer := none } := by
  classical
  let cfg1 : StackConfig Q r :=
    { state := restore,
      regs := Function.update (Function.update (Function.update cfg.regs src []) dst
        (w.reverse ++ cfg.regs dst)) tmp (w.reverse ++ cfg.regs tmp), answer := none }
  have hs1 : P.exec A cfg (3 * w.length + 1) = cfg1 :=
    stack_distribute_routine P A src dst tmp hsd hst hdt loop zero one zero' one' restore
      hloop hzero hone hzero' hone' cfg hs ha w hw
  have hw1 : cfg1.regs tmp = w.reverse := by simp [cfg1, htmp]
  have hs2 := stack_reverse_routine P A tmp src (Ne.symm hst) restore restoreZero restoreOne finish
    hrestore hrestoreZero hrestoreOne cfg1 rfl rfl w.reverse hw1
  rw [show 5 * w.length + 2 = (3 * w.length + 1) + (2 * w.reverse.length + 1) by simp; omega,
    StackProgram.exec_add, hs1, hs2]
  congr 1
  funext j
  by_cases hjs : j = src
  · subst j
    simp [cfg1, Function.update, hsd, hst, Ne.symm hsd, Ne.symm hst, hw]
  · by_cases hjd : j = dst
    · subst j
      simp [cfg1, Function.update, hsd, hdt, Ne.symm hsd, Ne.symm hdt]
    · by_cases hjt : j = tmp
      · subst j
        simp [cfg1, Function.update, hst, hdt, Ne.symm hst, Ne.symm hdt]
      · simp [cfg1, Function.update, hjs, hjd, hjt]

lemma stack_copy_word_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src dst tmp scratch : Fin (r + 2))
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hss : src ≠ scratch)
    (hdt : dst ≠ tmp) (hds : dst ≠ scratch) (hts : tmp ≠ scratch)
    (loop zero one zero' one' restore restoreZero restoreOne reverseLoop reverseZero reverseOne finish : Q)
    (hloop : P.transition loop = .pop src zero one restore)
    (hzero : P.transition zero = .push scratch false zero')
    (hone : P.transition one = .push scratch true one')
    (hzero' : P.transition zero' = .push tmp false loop)
    (hone' : P.transition one' = .push tmp true loop)
    (hrestore : P.transition restore = .pop tmp restoreZero restoreOne reverseLoop)
    (hrestoreZero : P.transition restoreZero = .push src false restore)
    (hrestoreOne : P.transition restoreOne = .push src true restore)
    (hreverse : P.transition reverseLoop = .pop scratch reverseZero reverseOne finish)
    (hreverseZero : P.transition reverseZero = .push dst false reverseLoop)
    (hreverseOne : P.transition reverseOne = .push dst true reverseLoop)
    (cfg : StackConfig Q r) (hs : cfg.state = loop) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) (htmp : cfg.regs tmp = []) (hscratch : cfg.regs scratch = []) :
    P.exec A cfg (7 * w.length + 3) =
      { state := finish,
        regs := Function.update (Function.update (Function.update cfg.regs dst (w ++ cfg.regs dst)) tmp []) scratch [],
        answer := none } := by
  classical
  let cfg1 : StackConfig Q r :=
    { state := reverseLoop,
      regs := Function.update (Function.update cfg.regs scratch (w.reverse ++ cfg.regs scratch)) tmp [], answer := none }
  have hs1 : P.exec A cfg (5 * w.length + 2) = cfg1 :=
    stack_copy_reverse_routine P A src scratch tmp hss hst (Ne.symm hts)
      loop zero one zero' one' restore restoreZero restoreOne reverseLoop
      hloop hzero hone hzero' hone' hrestore hrestoreZero hrestoreOne cfg hs ha w hw htmp
  have hw1 : cfg1.regs scratch = w.reverse := by simp [cfg1, hscratch, Ne.symm hts]
  have hs2 := stack_reverse_routine P A scratch dst (Ne.symm hds) reverseLoop reverseZero reverseOne finish
    hreverse hreverseZero hreverseOne cfg1 rfl rfl w.reverse hw1
  rw [show 7 * w.length + 3 = (5 * w.length + 2) + (2 * w.reverse.length + 1) by simp; omega,
    StackProgram.exec_add, hs1, hs2]
  congr 1
  funext j
  by_cases hjd : j = dst
  · subst j
    simp [cfg1, Function.update, hdt, hds, Ne.symm hdt, Ne.symm hds]
  · by_cases hjt : j = tmp
    · subst j
      simp [cfg1, Function.update, hdt, hts, Ne.symm hdt, Ne.symm hts]
    · by_cases hjs : j = scratch
      · subst j
        simp [cfg1, Function.update, hds, hts, Ne.symm hds, Ne.symm hts]
      · simp [cfg1, Function.update, hjd, hjt, hjs]

end APSCounting893.Main
end Component_11

section Component_12

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_prepend_nat_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (first second dst : Fin (r + 2)) (hfs : first ≠ second) (hfd : first ≠ dst) (hsd : second ≠ dst)
    (reverseLoop zero one delimiter prefixLoop prefixSave finish : Q)
    (hreverse : P.transition reverseLoop = .pop first zero one delimiter)
    (hzero : P.transition zero = .push dst false reverseLoop)
    (hone : P.transition one = .push dst true reverseLoop)
    (hdelimiter : P.transition delimiter = .push dst false prefixLoop)
    (hprefix : P.transition prefixLoop = .pop second prefixSave prefixSave finish)
    (hsave : P.transition prefixSave = .push dst true prefixLoop)
    (cfg : StackConfig Q r) (hs : cfg.state = reverseLoop) (ha : cfg.answer = none)
    (n : ℕ) (hfirst : cfg.regs first = n.bits.reverse) (hsecond : cfg.regs second = n.bits.reverse) :
    P.exec A cfg (4 * n.bits.length + 3) =
      { state := finish,
        regs := Function.update (Function.update (Function.update cfg.regs first []) second [])
          dst (encodeNat n ++ cfg.regs dst), answer := none } := by
  classical
  let cfg1 : StackConfig Q r :=
    { state := delimiter,
      regs := Function.update (Function.update cfg.regs first []) dst (n.bits ++ cfg.regs dst), answer := none }
  have hs1 : P.exec A cfg (2 * n.bits.length + 1) = cfg1 := by
    simpa only [List.length_reverse, List.reverse_reverse] using
      stack_reverse_routine P A first dst hfd reverseLoop zero one delimiter hreverse hzero hone cfg hs ha n.bits.reverse hfirst
  let cfg2 : StackConfig Q r :=
    { state := prefixLoop, regs := Function.update cfg1.regs dst (false :: (n.bits ++ cfg.regs dst)), answer := none }
  have hs2 : P.step A cfg1 = cfg2 := by
    simp [StackProgram.step, cfg1, cfg2, hdelimiter]
  have hw2 : cfg2.regs second = n.bits.reverse := by
    simp [cfg2, cfg1, hfs, Ne.symm hfs, hsd, hsecond]
  have hs3 := stack_map_reverse_routine P A (fun _ => true) second dst hsd prefixLoop prefixSave prefixSave finish
    hprefix hsave hsave cfg2 rfl rfl n.bits.reverse hw2
  rw [show 4 * n.bits.length + 3 = (2 * n.bits.length + 1) +
      (1 + (2 * n.bits.reverse.length + 1)) by simp; omega,
    StackProgram.exec_add, hs1, StackProgram.exec_add, StackProgram.exec_one, hs2, hs3]
  congr 1
  funext j
  by_cases hjf : j = first
  · subst j
    simp [cfg2, cfg1, Function.update, hfs, hfd, Ne.symm hfs, Ne.symm hfd]
  · by_cases hjs : j = second
    · subst j
      simp [cfg2, cfg1, Function.update, hsd, Ne.symm hsd]
    · by_cases hjd : j = dst
      · subst j
        simp [cfg2, cfg1, Function.update, hfd, hsd, Ne.symm hfd, Ne.symm hsd,
          encodeNat, List.append_assoc]
      · simp [cfg2, cfg1, Function.update, hjf, hjs, hjd]

end APSCounting893.Main
end Component_12

section Component_13

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def carryBits : Word → ℕ × Word
  | [] => (0, [])
  | false :: w => (0, w)
  | true :: w => let c := carryBits w; (c.1 + 1, c.2)

lemma incrementBits_eq_carryBits (w : Word) :
    incrementBits w = List.replicate (carryBits w).1 false ++ true :: (carryBits w).2 := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [carryBits, incrementBits, ih, List.replicate_succ]

lemma carryBits_count_le (w : Word) : (carryBits w).1 ≤ w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [carryBits] <;> omega

lemma stack_carry_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (counter tmp : Fin (r + 2)) (hne : counter ≠ tmp) (carry stop save restore : Q)
    (hcarry : P.transition carry = .pop counter stop save stop)
    (hstop : P.transition stop = .push counter true restore)
    (hsave : P.transition save = .push tmp false carry)
    (cfg : StackConfig Q r) (hs : cfg.state = carry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs counter = w) :
    P.exec A cfg (2 * ((carryBits w).1 + 1)) =
      { state := restore,
        regs := Function.update (Function.update cfg.regs counter (true :: (carryBits w).2)) tmp
          (List.replicate (carryBits w).1 false ++ cfg.regs tmp), answer := none } := by
  classical
  induction w generalizing cfg with
  | nil =>
      change P.step A (P.step A cfg) = _
      simp [StackProgram.step, hs, ha, hcarry, hstop, hw, carryBits, Ne.symm hne]
  | cons b w ih =>
      cases b with
      | false =>
          change P.step A (P.step A cfg) = _
          simp [StackProgram.step, hs, ha, hcarry, hstop, hw, carryBits, Ne.symm hne]
      | true =>
          let cfg1 : StackConfig Q r :=
            { state := save, regs := Function.update cfg.regs counter w, answer := none }
          let cfg2 : StackConfig Q r :=
            { state := carry, regs := Function.update (Function.update cfg.regs counter w) tmp
                (false :: cfg.regs tmp), answer := none }
          have hstep1 : P.step A cfg = cfg1 := by
            simp [StackProgram.step, hs, ha, hcarry, hw, cfg1]
          have hstep2 : P.step A cfg1 = cfg2 := by
            simp [StackProgram.step, hsave, cfg1, cfg2, Ne.symm hne]
          have hsrc : cfg2.regs counter = w := by simp [cfg2, hne]
          have hrec := ih cfg2 rfl rfl hsrc
          rw [show 2 * ((carryBits (true :: w)).1 + 1) =
              1 + (1 + (2 * ((carryBits w).1 + 1))) by simp [carryBits]; omega,
            StackProgram.exec_add, StackProgram.exec_one, hstep1,
            StackProgram.exec_add, StackProgram.exec_one, hstep2, hrec]
          congr 1
          funext j
          by_cases hjc : j = counter
          · subst j
            simp [cfg2, carryBits, Function.update, hne, Ne.symm hne]
          · by_cases hjt : j = tmp
            · subst j
              simp [cfg2, carryBits, Function.update, hne, Ne.symm hne, List.replicate_succ', List.append_assoc]
            · simp [cfg2, carryBits, Function.update, hjc, hjt]

lemma stack_increment_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (counter tmp : Fin (r + 2)) (hne : counter ≠ tmp)
    (carry stop save restore zero one finish : Q)
    (hcarry : P.transition carry = .pop counter stop save stop)
    (hstop : P.transition stop = .push counter true restore)
    (hsave : P.transition save = .push tmp false carry)
    (hrestore : P.transition restore = .pop tmp zero one finish)
    (hzero : P.transition zero = .push counter false restore)
    (hone : P.transition one = .push counter true restore)
    (cfg : StackConfig Q r) (hs : cfg.state = carry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs counter = w) (htmp : cfg.regs tmp = []) :
    P.exec A cfg (4 * (carryBits w).1 + 3) =
      { state := finish,
        regs := Function.update (Function.update cfg.regs counter (incrementBits w)) tmp [], answer := none } := by
  classical
  let cfg1 : StackConfig Q r :=
    { state := restore,
      regs := Function.update (Function.update cfg.regs counter (true :: (carryBits w).2)) tmp
        (List.replicate (carryBits w).1 false ++ cfg.regs tmp), answer := none }
  have hs1 : P.exec A cfg (2 * ((carryBits w).1 + 1)) = cfg1 :=
    stack_carry_routine P A counter tmp hne carry stop save restore hcarry hstop hsave cfg hs ha w hw
  have hw1 : cfg1.regs tmp = List.replicate (carryBits w).1 false := by simp [cfg1, htmp]
  have hs2 := stack_reverse_routine P A tmp counter (Ne.symm hne) restore zero one finish
    hrestore hzero hone cfg1 rfl rfl (List.replicate (carryBits w).1 false) hw1
  rw [show 4 * (carryBits w).1 + 3 = 2 * ((carryBits w).1 + 1) +
      (2 * (List.replicate (carryBits w).1 false).length + 1) by simp; omega,
    StackProgram.exec_add, hs1, hs2]
  congr 1
  funext j
  by_cases hjc : j = counter
  · subst j
    simp [cfg1, Function.update, hne, Ne.symm hne, List.reverse_replicate, incrementBits_eq_carryBits]
  · by_cases hjt : j = tmp
    · subst j
      simp [cfg1, Function.update, hne, Ne.symm hne]
    · simp [cfg1, Function.update, hjc, hjt]

end APSCounting893.Main
end Component_13

section Component_14

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def lengthCountTime (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => 1 + (4 * (carryBits n.bits).1 + 3) + lengthCountTime (n + 1) m

lemma lengthCountTime_bound (n m : ℕ) :
    lengthCountTime n m ≤ (4 * (n + m + 1) + 4) * m + 1 := by
  induction m generalizing n with
  | zero => simp [lengthCountTime]
  | succ m ih =>
      have hbits : n.bits.length ≤ n := by
        rw [Nat.size_eq_bits_len]
        exact Nat.size_le.mpr n.lt_two_pow_self
      have hc := (carryBits_count_le n.bits).trans hbits
      have hn := ih (n + 1)
      simp only [lengthCountTime]
      nlinarith

lemma stack_length_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src counter tmp : Fin (r + 2)) (hsc : src ≠ counter) (hst : src ≠ tmp) (hct : counter ≠ tmp)
    (countLoop carry stop save restore zero one finish : Q)
    (hcount : P.transition countLoop = .pop src carry carry finish)
    (hcarry : P.transition carry = .pop counter stop save stop)
    (hstop : P.transition stop = .push counter true restore)
    (hsave : P.transition save = .push tmp false carry)
    (hrestore : P.transition restore = .pop tmp zero one countLoop)
    (hzero : P.transition zero = .push counter false restore)
    (hone : P.transition one = .push counter true restore)
    (cfg : StackConfig Q r) (hs : cfg.state = countLoop) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) (n : ℕ) (hn : cfg.regs counter = n.bits)
    (htmp : cfg.regs tmp = []) :
    P.exec A cfg (lengthCountTime n w.length) =
      { state := finish, regs := Function.update (Function.update (Function.update cfg.regs src [])
          counter (n + w.length).bits) tmp [], answer := none } := by
  classical
  induction w generalizing cfg n with
  | nil =>
      change P.step A cfg = _
      have hup : Function.update cfg.regs src [] = cfg.regs := by rw [← hw]; exact Function.update_eq_self src cfg.regs
      have hupc : Function.update cfg.regs counter n.bits = cfg.regs := by
        rw [← hn]
        exact Function.update_eq_self counter cfg.regs
      have hupt : Function.update cfg.regs tmp [] = cfg.regs := by
        rw [← htmp]
        exact Function.update_eq_self tmp cfg.regs
      simp [StackProgram.step, hs, ha, hcount, hw, hup, hupc, hupt]
  | cons b w ih =>
      let cfg1 : StackConfig Q r :=
        { state := carry, regs := Function.update cfg.regs src w, answer := none }
      let cfg2 : StackConfig Q r :=
        { state := countLoop, regs := Function.update (Function.update cfg1.regs counter (incrementBits n.bits)) tmp [],
          answer := none }
      have hs1 : P.step A cfg = cfg1 := by
        cases b <;> simp [StackProgram.step, hs, ha, hcount, hw, cfg1]
      have hn1 : cfg1.regs counter = n.bits := by simp [cfg1, Ne.symm hsc, hn]
      have ht1 : cfg1.regs tmp = [] := by simp [cfg1, Ne.symm hst, htmp]
      have hs2 : P.exec A cfg1 (4 * (carryBits n.bits).1 + 3) = cfg2 :=
        stack_increment_routine P A counter tmp hct carry stop save restore zero one countLoop
          hcarry hstop hsave hrestore hzero hone cfg1 rfl rfl n.bits hn1 ht1
      have hw2 : cfg2.regs src = w := by simp [cfg2, cfg1, hsc, hst]
      have hn2 : cfg2.regs counter = (n + 1).bits := by simp [cfg2, hct, incrementBits_nat_bits]
      have ht2 : cfg2.regs tmp = [] := by simp [cfg2]
      have hrec := ih cfg2 rfl rfl hw2 (n + 1) hn2 ht2
      rw [show lengthCountTime n (b :: w).length =
          1 + ((4 * (carryBits n.bits).1 + 3) + lengthCountTime (n + 1) w.length) by
            simp only [List.length_cons, lengthCountTime]; omega,
        StackProgram.exec_add, StackProgram.exec_one, hs1,
        StackProgram.exec_add, hs2, hrec]
      congr 1
      funext j
      by_cases hjs : j = src
      · subst j
        simp [cfg2, cfg1, Function.update, hsc, hst, Ne.symm hsc, Ne.symm hst]
      · by_cases hjc : j = counter
        · subst j
          simp [cfg2, cfg1, Function.update, hct, Ne.symm hct, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        · by_cases hjt : j = tmp
          · subst j
            simp [cfg2, cfg1, Function.update, hct, Ne.symm hct]
          · simp [cfg2, cfg1, Function.update, hjs, hjc, hjt]

end APSCounting893.Main
end Component_14

section Component_15
set_option autoImplicit false
namespace APSCounting893.Main
lemma arithmeticAssemble_reverse {Q : Type} [Fintype Q] {r : ℕ} (table : Q → ArithmeticWordOp Q r) (initial q next : Q)
    (A : Language) (src dst : Fin (r + 2)) (hne : src ≠ dst)
    (ht : table q = .reverse src dst next)
    (cfg : StackConfig (ArithmeticAssemblyControl Q (arithmeticAssemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none) (w : Word) (hw : cfg.regs src = w) :
    (arithmeticAssemble table initial).exec A cfg (2 * w.length + 1) =
      { state := .at next .entry, regs := Function.update (Function.update cfg.regs src []) dst
          (w.reverse ++ cfg.regs dst), answer := none } := by
  apply stack_reverse_routine (arithmeticAssemble table initial) A src dst hne (.at q .entry) (.at q .p1) (.at q .p2) (.at next .entry)
    (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht]) cfg hs ha w hw

lemma arithmeticAssemble_copy {Q : Type} [Fintype Q] {r : ℕ} (table : Q → ArithmeticWordOp Q r) (initial q next : Q)
    (A : Language) (src dst tmp scratch : Fin (r + 2))
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hss : src ≠ scratch)
    (hdt : dst ≠ tmp) (hds : dst ≠ scratch) (hts : tmp ≠ scratch)
    (ht : table q = .copy src dst tmp scratch next)
    (cfg : StackConfig (ArithmeticAssemblyControl Q (arithmeticAssemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) (htmp : cfg.regs tmp = []) (hscratch : cfg.regs scratch = []) :
    (arithmeticAssemble table initial).exec A cfg (7 * w.length + 3) =
      { state := .at next .entry,
        regs := Function.update (Function.update (Function.update cfg.regs dst (w ++ cfg.regs dst)) tmp []) scratch [],
        answer := none } := by
  exact stack_copy_word_routine (arithmeticAssemble table initial) A src dst tmp scratch hsd hst hss hdt hds hts
    (.at q .entry) (.at q .p1) (.at q .p2) (.at q .p3) (.at q .p4) (.at q .p5)
    (.at q .p6) (.at q .p7) (.at q .p8) (.at q .p9) (.at q .p10) (.at next .entry)
    (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht])
    (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht])
    (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht])
    (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht]) cfg hs ha w hw htmp hscratch

lemma arithmeticAssemble_length {Q : Type} [Fintype Q] {r : ℕ} (table : Q → ArithmeticWordOp Q r) (initial q next : Q)
    (A : Language) (src counter tmp : Fin (r + 2)) (hsc : src ≠ counter) (hst : src ≠ tmp) (hct : counter ≠ tmp)
    (ht : table q = .length src counter tmp next)
    (cfg : StackConfig (ArithmeticAssemblyControl Q (arithmeticAssemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) (n : ℕ) (hn : cfg.regs counter = n.bits) (htmp : cfg.regs tmp = []) :
    (arithmeticAssemble table initial).exec A cfg (lengthCountTime n w.length) =
      { state := .at next .entry, regs := Function.update (Function.update (Function.update cfg.regs src [])
          counter (n + w.length).bits) tmp [], answer := none } := by
  exact stack_length_routine (arithmeticAssemble table initial) A src counter tmp hsc hst hct
    (.at q .entry) (.at q .p1) (.at q .p2) (.at q .p3) (.at q .p4) (.at q .p5) (.at q .p6) (.at next .entry)
    (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht])
    (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht])
    cfg hs ha w hw n hn htmp

lemma arithmeticAssemble_encodeNat {Q : Type} [Fintype Q] {r : ℕ} (table : Q → ArithmeticWordOp Q r) (initial q next : Q)
    (A : Language) (first second dst : Fin (r + 2)) (hfs : first ≠ second) (hfd : first ≠ dst) (hsd : second ≠ dst)
    (ht : table q = .encodeNat first second dst next)
    (cfg : StackConfig (ArithmeticAssemblyControl Q (arithmeticAssemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none)
    (n : ℕ) (hfirst : cfg.regs first = n.bits.reverse) (hsecond : cfg.regs second = n.bits.reverse) :
    (arithmeticAssemble table initial).exec A cfg (4 * n.bits.length + 3) =
      { state := .at next .entry, regs := Function.update (Function.update (Function.update cfg.regs first []) second [])
          dst (encodeNat n ++ cfg.regs dst), answer := none } := by
  exact stack_prepend_nat_routine (arithmeticAssemble table initial) A first second dst hfs hfd hsd
    (.at q .entry) (.at q .p1) (.at q .p2) (.at q .p3) (.at q .p4) (.at q .p5) (.at next .entry)
    (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht])
    (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht]) (by simp [arithmeticAssemble, ht])
    cfg hs ha n hfirst hsecond


end APSCounting893.Main
end Component_15

section Component_16
set_option autoImplicit false
namespace APSCounting893.Main
lemma StackProgram.functionInPWithOracle {Q : Type} [Fintype Q] {r : ℕ}
    (P : StackProgram Q r) (A : Language) (f : Word → Word)
    (stop : Q) (src : Fin (r+2)) (hstop : P.transition stop=.halt true) (c d : ℕ)
    (h : ∀ x : Word,∃ T≤polyBound c d x.length,
      (P.run A x [] T).state=stop ∧ (P.run A x [] T).answer=none ∧ (P.run A x [] T).regs src=f x) :
    FunctionInPWithOracle A f := by
  exact stack_function_polynomial_simulation P A f stop src hstop c d h

end APSCounting893.Main
end Component_16

section Component_17
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

inductive OracleMaxSite where
  | initCopy | initReverse | copyCount | reverseCount | copyRev | encode | delimiter | copyInput | escape | query
  | yesClear | yesCopy | budget | incPush | incLength
  | finishCopy | finishReverse | finishCopyRev | finishEncode | done
  deriving DecidableEq,Fintype

def oracleMaxTable : OracleMaxSite → ArithmeticWordOp OracleMaxSite 10
  | .initCopy=>.copy 0 2 9 10 .initReverse
  | .initReverse=>.reverse 0 3 .copyCount
  | .copyCount=>.copy 4 6 9 10 .reverseCount
  | .reverseCount=>.reverse 6 7 .copyRev
  | .copyRev=>.copy 7 8 9 10 .encode
  | .encode=>.encodeNat 7 8 11 .delimiter
  | .delimiter=>.push 11 false .copyInput
  | .copyInput=>.copy 3 6 9 10 .escape
  | .escape=>.escape 6 11 .query
  | .query=>.query 11 .yesClear .budget
  | .yesClear=>.clear 5 .yesCopy
  | .yesCopy=>.copy 4 5 9 10 .budget
  | .budget=>.pop 2 .incPush .incPush .finishCopy
  | .incPush=>.push 6 true .incLength
  | .incLength=>.length 6 4 9 .copyCount
  | .finishCopy=>.copy 5 6 9 10 .finishReverse
  | .finishReverse=>.reverse 6 7 .finishCopyRev
  | .finishCopyRev=>.copy 7 8 9 10 .finishEncode
  | .finishEncode=>.encodeNat 7 8 11 .done
  | .done=>.halt true

noncomputable def oracleMaxProgram:=arithmeticAssemble oracleMaxTable .initCopy
abbrev OracleMaxControl:=ArithmeticAssemblyControl OracleMaxSite (arithmeticAssemblyConstantBound oracleMaxTable)

def oracleMaxRegs (budget inputRev : Word) (k result : ℕ) : Fin 12 → Word :=
  fun j=>if j=2 then budget else if j=3 then inputRev else if j=4 then k.bits else if j=5 then result.bits else []

def oracleMaxConfig (site : OracleMaxSite) (budget inputRev : Word) (k result : ℕ) :
    StackConfig OracleMaxControl 10 :=
  {state:=.at site .entry,regs:=oracleMaxRegs budget inputRev k result,answer:=none}

open scoped Classical in
noncomputable def boundedOracleMaxAux (A : Language) (x : Word) : ℕ → ℕ → ℕ → ℕ
  | 0,k,result=>if A (pairWord x (encodeNat k)) then k else result
  | fuel+1,k,result=>boundedOracleMaxAux A x fuel (k+1) (if A (pairWord x (encodeNat k)) then k else result)

noncomputable def boundedOracleMaximum (A : Language) (x : Word) : ℕ:=boundedOracleMaxAux A x x.length 0 0

end APSCounting893.Main
end Component_17

section Component_18
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def oracleQueryConfig (site : OracleMaxSite) (budget inputRev : Word) (k result : ℕ)
    (query work first second : Word) : StackConfig OracleMaxControl 10 :=
  {state:=.at site .entry,regs:=fun j=>
    if j=2 then budget else if j=3 then inputRev else if j=4 then k.bits else if j=5 then result.bits
    else if j=6 then work else if j=7 then first else if j=8 then second else if j=11 then query else [],answer:=none}

lemma oracleMax_query_builder (A : Language) (budget x : Word) (k result : ℕ) :
    oracleMaxProgram.exec A (oracleMaxConfig .copyCount budget x.reverse k result)
      (20*k.bits.length+10*x.length+15)=
      oracleQueryConfig .query budget x.reverse k result (pairWord x (encodeNat k)) [] [] [] := by
  classical
  let cfg0:=oracleQueryConfig .copyCount budget x.reverse k result ([]) ([]) ([]) ([])
  let cfg1:=oracleQueryConfig .reverseCount budget x.reverse k result ([]) (k.bits) ([]) ([])
  let cfg2:=oracleQueryConfig .copyRev budget x.reverse k result ([]) ([]) (k.bits.reverse) ([])
  let cfg3:=oracleQueryConfig .encode budget x.reverse k result ([]) ([]) (k.bits.reverse) (k.bits.reverse)
  let cfg4:=oracleQueryConfig .delimiter budget x.reverse k result (encodeNat k) ([]) ([]) ([])
  let cfg5:=oracleQueryConfig .copyInput budget x.reverse k result (false::encodeNat k) ([]) ([]) ([])
  let cfg6:=oracleQueryConfig .escape budget x.reverse k result (false::encodeNat k) (x.reverse) ([]) ([])
  let cfg7:=oracleQueryConfig .query budget x.reverse k result (pairWord x (encodeNat k)) ([]) ([]) ([])
  have hinit : oracleMaxConfig .copyCount budget x.reverse k result=cfg0 := by
    dsimp only [oracleMaxConfig,cfg0,oracleQueryConfig]
    congr 1
    funext j
    fin_cases j <;> simp [oracleMaxRegs]
  have h1 : oracleMaxProgram.exec A cfg0 (7*k.bits.length+3)=cfg1 := by
    have hh:=arithmeticAssemble_copy oracleMaxTable .initCopy .copyCount .reverseCount A 4 6 9 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl cfg0 rfl rfl k.bits (by simp [cfg0,oracleQueryConfig]) (by simp [cfg0,oracleQueryConfig]) (by simp [cfg0,oracleQueryConfig])
    try simp only [List.length_reverse] at hh
    unfold oracleMaxProgram
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [cfg0,cfg1,oracleQueryConfig,pairWord]
  have h2 : oracleMaxProgram.exec A cfg1 (2*k.bits.length+1)=cfg2 := by
    have hh:=arithmeticAssemble_reverse oracleMaxTable .initCopy .reverseCount .copyRev A 6 7 (by decide) rfl cfg1 rfl rfl k.bits (by simp [cfg1,oracleQueryConfig])
    try simp only [List.length_reverse] at hh
    unfold oracleMaxProgram
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [cfg1,cfg2,oracleQueryConfig,pairWord]
  have h3 : oracleMaxProgram.exec A cfg2 (7*k.bits.length+3)=cfg3 := by
    have hh:=arithmeticAssemble_copy oracleMaxTable .initCopy .copyRev .encode A 7 8 9 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl cfg2 rfl rfl k.bits.reverse (by simp [cfg2,oracleQueryConfig]) (by simp [cfg2,oracleQueryConfig]) (by simp [cfg2,oracleQueryConfig])
    try simp only [List.length_reverse] at hh
    unfold oracleMaxProgram
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [cfg2,cfg3,oracleQueryConfig,pairWord]
  have h4 : oracleMaxProgram.exec A cfg3 (4*k.bits.length+3)=cfg4 := by
    have hh:=arithmeticAssemble_encodeNat oracleMaxTable .initCopy .encode .delimiter A 7 8 11 (by decide) (by decide) (by decide) rfl cfg3 rfl rfl k (by simp [cfg3,oracleQueryConfig]) (by simp [cfg3,oracleQueryConfig])
    try simp only [List.length_reverse] at hh
    unfold oracleMaxProgram
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [cfg3,cfg4,oracleQueryConfig,pairWord]
  have h5 : oracleMaxProgram.exec A cfg4 (1)=cfg5 := by
    rw [StackProgram.exec_one]
    simp only [StackProgram.step,oracleMaxProgram,arithmeticAssemble,oracleMaxTable]
    simp [cfg4,cfg5,oracleQueryConfig]
    congr 1
    funext j
    fin_cases j <;> simp [cfg4,cfg5,oracleQueryConfig]
  have h6 : oracleMaxProgram.exec A cfg5 (7*x.length+3)=cfg6 := by
    have hh:=arithmeticAssemble_copy oracleMaxTable .initCopy .copyInput .escape A 3 6 9 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl cfg5 rfl rfl x.reverse (by simp [cfg5,oracleQueryConfig]) (by simp [cfg5,oracleQueryConfig]) (by simp [cfg5,oracleQueryConfig])
    try simp only [List.length_reverse] at hh
    unfold oracleMaxProgram
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [cfg5,cfg6,oracleQueryConfig,pairWord]
  have h7 : oracleMaxProgram.exec A cfg6 (3*x.length+1)=cfg7 := by
    have hh:=arithmeticAssemble_escape oracleMaxTable .initCopy .escape .query A 6 11 (by decide) rfl cfg6 rfl rfl x.reverse (by simp [cfg6,oracleQueryConfig])
    try simp only [List.length_reverse] at hh
    unfold oracleMaxProgram
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [cfg6,cfg7,oracleQueryConfig,pairWord]
  have htime : 20*k.bits.length+10*x.length+15=
      (7*k.bits.length+3)+((2*k.bits.length+1)+((7*k.bits.length+3)+((4*k.bits.length+3)+(1+((7*x.length+3)+(3*x.length+1)))))) := by omega
  rw [hinit,htime,StackProgram.exec_add,h1,StackProgram.exec_add,h2,StackProgram.exec_add,h3,
    StackProgram.exec_add,h4,StackProgram.exec_add,h5,StackProgram.exec_add,h6,h7]

end APSCounting893.Main
end Component_18

section Component_19
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open scoped Classical

lemma oracleMax_query_step (A : Language) (budget x : Word) (k result : ℕ) :
    oracleMaxProgram.step A (oracleQueryConfig .query budget x.reverse k result (pairWord x (encodeNat k)) [] [] [])=
      oracleMaxConfig (if A (pairWord x (encodeNat k)) then .yesClear else .budget) budget x.reverse k result := by
  classical
  by_cases hA : A (pairWord x (encodeNat k)) <;>
    simp only [StackProgram.step,oracleMaxProgram,arithmeticAssemble,oracleMaxTable,oracleQueryConfig]
  all_goals simp [hA,oracleMaxConfig,oracleMaxRegs]
  all_goals congr 1;funext j;fin_cases j <;> simp [oracleMaxRegs]

lemma oracleMax_yes_update (A : Language) (budget inputRev : Word) (k result : ℕ) :
    oracleMaxProgram.exec A (oracleMaxConfig .yesClear budget inputRev k result)
      (result.bits.length+7*k.bits.length+4)=oracleMaxConfig .budget budget inputRev k k := by
  classical
  let cfg0:=oracleMaxConfig .yesClear budget inputRev k result
  let cfg1:=oracleMaxConfig .yesCopy budget inputRev k 0
  have hclear : oracleMaxProgram.exec A cfg0 (result.bits.length+1)=cfg1 := by
    have hh:=arithmeticAssemble_clear oracleMaxTable .initCopy .yesClear .yesCopy A 5 rfl cfg0 rfl rfl result.bits
      (by simp [cfg0,oracleMaxConfig,oracleMaxRegs])
    unfold oracleMaxProgram
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [cfg0,cfg1,oracleMaxConfig,oracleMaxRegs]
  have hcopy : oracleMaxProgram.exec A cfg1 (7*k.bits.length+3)=oracleMaxConfig .budget budget inputRev k k := by
    have hh:=arithmeticAssemble_copy oracleMaxTable .initCopy .yesCopy .budget A 4 5 9 10
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl cfg1 rfl rfl k.bits
      (by simp [cfg1,oracleMaxConfig,oracleMaxRegs]) (by simp [cfg1,oracleMaxConfig,oracleMaxRegs])
      (by simp [cfg1,oracleMaxConfig,oracleMaxRegs])
    unfold oracleMaxProgram
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [cfg1,oracleMaxConfig,oracleMaxRegs]
  rw [show result.bits.length+7*k.bits.length+4=(result.bits.length+1)+(7*k.bits.length+3) by omega,
    StackProgram.exec_add]
  change oracleMaxProgram.exec A (oracleMaxProgram.exec A cfg0 _) _=_
  rw [hclear,hcopy]

end APSCounting893.Main
end Component_19

section Component_20
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma oracleMax_budget_empty (A : Language) (inputRev : Word) (k result : ℕ) :
    oracleMaxProgram.step A (oracleMaxConfig .budget [] inputRev k result)=oracleMaxConfig .finishCopy [] inputRev k result := by
  simp only [StackProgram.step,oracleMaxProgram,arithmeticAssemble,oracleMaxTable,oracleMaxConfig,oracleMaxRegs]
  simp [oracleMaxRegs]

lemma oracleMax_budget_nonempty (A : Language) (b : Bool) (budget inputRev : Word) (k result : ℕ) :
    oracleMaxProgram.exec A (oracleMaxConfig .budget (b::budget) inputRev k result)
      (2+lengthCountTime k 1)=oracleMaxConfig .copyCount budget inputRev (k+1) result := by
  classical
  let cfg1:=oracleMaxConfig .incPush budget inputRev k result
  let cfg2 : StackConfig OracleMaxControl 10:=
    {state:=.at .incLength .entry,regs:=Function.update cfg1.regs 6 [true],answer:=none}
  have hpop : oracleMaxProgram.step A (oracleMaxConfig .budget (b::budget) inputRev k result)=cfg1 := by
    cases b <;> simp only [StackProgram.step,oracleMaxProgram,arithmeticAssemble,oracleMaxTable,oracleMaxConfig,oracleMaxRegs]
    all_goals simp
    all_goals congr 1;funext j;fin_cases j <;> simp [cfg1,oracleMaxConfig,oracleMaxRegs]
  have hpush : oracleMaxProgram.step A cfg1=cfg2 := by
    simp [StackProgram.step,oracleMaxProgram,arithmeticAssemble,oracleMaxTable,cfg1,cfg2,oracleMaxConfig,oracleMaxRegs]
  have hlength : oracleMaxProgram.exec A cfg2 (lengthCountTime k 1)=oracleMaxConfig .copyCount budget inputRev (k+1) result := by
    have hh:=arithmeticAssemble_length oracleMaxTable .initCopy .incLength .copyCount A 6 4 9
      (by decide) (by decide) (by decide) rfl cfg2 rfl rfl [true] (by simp [cfg2]) k
      (by simp [cfg2,cfg1,oracleMaxConfig,oracleMaxRegs]) (by simp [cfg2,cfg1,oracleMaxConfig,oracleMaxRegs])
    simp only [List.length_cons,List.length_nil] at hh
    unfold oracleMaxProgram
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [cfg2,cfg1,oracleMaxConfig,oracleMaxRegs]
  rw [show 2+lengthCountTime k 1=1+(1+lengthCountTime k 1) by omega,StackProgram.exec_add,StackProgram.exec_one,hpop,
    StackProgram.exec_add,StackProgram.exec_one,hpush,hlength]

end APSCounting893.Main
end Component_20

section Component_21
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma oracleMax_finish_encode (A : Language) (budget inputRev : Word) (k result : ℕ) :
    oracleMaxProgram.exec A (oracleMaxConfig .finishCopy budget inputRev k result)
      (20*result.bits.length+10)=
      oracleQueryConfig .done budget inputRev k result (encodeNat result) [] [] [] := by
  classical
  let cfg0:=oracleQueryConfig .finishCopy budget inputRev k result ([]) ([]) ([]) ([])
  let cfg1:=oracleQueryConfig .finishReverse budget inputRev k result ([]) (result.bits) ([]) ([])
  let cfg2:=oracleQueryConfig .finishCopyRev budget inputRev k result ([]) ([]) (result.bits.reverse) ([])
  let cfg3:=oracleQueryConfig .finishEncode budget inputRev k result ([]) ([]) (result.bits.reverse) (result.bits.reverse)
  let cfg4:=oracleQueryConfig .done budget inputRev k result (encodeNat result) ([]) ([]) ([])
  have hinit : oracleMaxConfig .finishCopy budget inputRev k result=cfg0 := by
    dsimp only [oracleMaxConfig,cfg0,oracleQueryConfig]
    congr 1
    funext j
    fin_cases j <;> simp [oracleMaxRegs]
  have h1 : oracleMaxProgram.exec A cfg0 (7*result.bits.length+3)=cfg1 := by
    have hh:=arithmeticAssemble_copy oracleMaxTable .initCopy .finishCopy .finishReverse A 5 6 9 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl cfg0 rfl rfl result.bits (by simp [cfg0,oracleQueryConfig]) (by simp [cfg0,oracleQueryConfig]) (by simp [cfg0,oracleQueryConfig])
    try simp only [List.length_reverse] at hh
    unfold oracleMaxProgram
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [cfg0,cfg1,oracleQueryConfig]
  have h2 : oracleMaxProgram.exec A cfg1 (2*result.bits.length+1)=cfg2 := by
    have hh:=arithmeticAssemble_reverse oracleMaxTable .initCopy .finishReverse .finishCopyRev A 6 7 (by decide) rfl cfg1 rfl rfl result.bits (by simp [cfg1,oracleQueryConfig])
    try simp only [List.length_reverse] at hh
    unfold oracleMaxProgram
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [cfg1,cfg2,oracleQueryConfig]
  have h3 : oracleMaxProgram.exec A cfg2 (7*result.bits.length+3)=cfg3 := by
    have hh:=arithmeticAssemble_copy oracleMaxTable .initCopy .finishCopyRev .finishEncode A 7 8 9 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl cfg2 rfl rfl result.bits.reverse (by simp [cfg2,oracleQueryConfig]) (by simp [cfg2,oracleQueryConfig]) (by simp [cfg2,oracleQueryConfig])
    try simp only [List.length_reverse] at hh
    unfold oracleMaxProgram
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [cfg2,cfg3,oracleQueryConfig]
  have h4 : oracleMaxProgram.exec A cfg3 (4*result.bits.length+3)=cfg4 := by
    have hh:=arithmeticAssemble_encodeNat oracleMaxTable .initCopy .finishEncode .done A 7 8 11 (by decide) (by decide) (by decide) rfl cfg3 rfl rfl result (by simp [cfg3,oracleQueryConfig]) (by simp [cfg3,oracleQueryConfig])
    try simp only [List.length_reverse] at hh
    unfold oracleMaxProgram
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [cfg3,cfg4,oracleQueryConfig]
  have htime : 20*result.bits.length+10=(7*result.bits.length+3)+((2*result.bits.length+1)+((7*result.bits.length+3)+(4*result.bits.length+3))) := by omega
  rw [hinit,htime,StackProgram.exec_add,h1,StackProgram.exec_add,h2,StackProgram.exec_add,h3,h4]

end APSCounting893.Main
end Component_21

section Component_22
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open scoped Classical

lemma oracleMax_query_and_update (A : Language) (budget x : Word) (k result : ℕ) :
    ∃ t≤20*k.bits.length+10*x.length+16+result.bits.length+7*k.bits.length+4,
      oracleMaxProgram.exec A (oracleMaxConfig .copyCount budget x.reverse k result) t=
        oracleMaxConfig .budget budget x.reverse k (if A (pairWord x (encodeNat k)) then k else result) := by
  by_cases hA : A (pairWord x (encodeNat k))
  · refine ⟨(20*k.bits.length+10*x.length+15)+(1+(result.bits.length+7*k.bits.length+4)),by omega,?_⟩
    rw [StackProgram.exec_add,oracleMax_query_builder,StackProgram.exec_add,StackProgram.exec_one,oracleMax_query_step]
    simp only [if_pos hA]
    exact oracleMax_yes_update A budget x.reverse k result
  · refine ⟨(20*k.bits.length+10*x.length+15)+1,by omega,?_⟩
    rw [StackProgram.exec_add,oracleMax_query_builder,StackProgram.exec_one,oracleMax_query_step]
    simp only [if_neg hA]

lemma oracleMax_loop (A : Language) (budget x : Word) (k result : ℕ)
    (hk : k+budget.length≤x.length) (hr : result≤k) :
    ∃ t≤100*(budget.length+1)*(x.length+1),
      oracleMaxProgram.exec A (oracleMaxConfig .copyCount budget x.reverse k result) t=
        oracleQueryConfig .done [] x.reverse (k+budget.length) (boundedOracleMaxAux A x budget.length k result)
          (encodeNat (boundedOracleMaxAux A x budget.length k result)) [] [] [] := by
  induction budget generalizing k result with
  | nil =>
    obtain ⟨t,ht,hrun⟩:=oracleMax_query_and_update A [] x k result
    let r:=if A (pairWord x (encodeNat k)) then k else result
    have hrr : r≤k := by dsimp [r];split_ifs <;> omega
    have hkb : k.bits.length≤x.length := by
      have hh : k.bits.length≤k := by simpa only [Nat.size_eq_bits_len] using (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=k)))
      simpa using hh.trans hk
    have hresb : result.bits.length≤x.length := by
      have hh : result.bits.length≤result := by simpa only [Nat.size_eq_bits_len] using (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=result)))
      omega
    have hrb : r.bits.length≤x.length := by
      have hh : r.bits.length≤r := by simpa only [Nat.size_eq_bits_len] using (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=r)))
      omega
    refine ⟨t+(1+(20*r.bits.length+10)),?_,?_⟩
    · simp only [List.length_nil,zero_add,one_mul]
      omega
    · rw [StackProgram.exec_add,hrun,StackProgram.exec_add,StackProgram.exec_one,oracleMax_budget_empty,oracleMax_finish_encode]
      simp [boundedOracleMaxAux,r]
  | cons b budget ih =>
    obtain ⟨t,ht,hrun⟩:=oracleMax_query_and_update A (b::budget) x k result
    let r:=if A (pairWord x (encodeNat k)) then k else result
    have hrr : r≤k := by dsimp [r];split_ifs <;> omega
    obtain ⟨u,hu,hrec⟩:=ih (k+1) r (by simp only [List.length_cons] at hk;omega) (by omega)
    have hkb : k.bits.length≤x.length := by
      have hh : k.bits.length≤k := by simpa only [Nat.size_eq_bits_len] using (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=k)))
      simp only [List.length_cons] at hk
      omega
    have hresb : result.bits.length≤x.length := by
      have hh : result.bits.length≤result := by simpa only [Nat.size_eq_bits_len] using (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=result)))
      simp only [List.length_cons] at hk
      omega
    have hinc:=lengthCountTime_bound k 1
    refine ⟨t+((2+lengthCountTime k 1)+u),?_,?_⟩
    · simp only [List.length_cons] at hk ⊢
      nlinarith
    · rw [StackProgram.exec_add,hrun,StackProgram.exec_add,oracleMax_budget_nonempty]
      change oracleMaxProgram.exec A (oracleMaxConfig .copyCount budget x.reverse (k+1) r) u=_
      rw [hrec]
      simp [boundedOracleMaxAux,r,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end APSCounting893.Main
end Component_22

section Component_23
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma oracleMax_initial (A : Language) (x : Word) :
    oracleMaxProgram.run A x [] (9*x.length+4)=oracleMaxConfig .copyCount x x.reverse 0 0 := by
  classical
  let cfg0:=oracleMaxProgram.initialConfig x []
  let cfg1 : StackConfig OracleMaxControl 10:=
    {state:=.at .initReverse .entry,regs:=fun j=>if j=0 then x else if j=2 then x else [],answer:=none}
  have hcopy : oracleMaxProgram.exec A cfg0 (7*x.length+3)=cfg1 := by
    have hh:=arithmeticAssemble_copy oracleMaxTable .initCopy .initCopy .initReverse A 0 2 9 10
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl cfg0 rfl rfl x
      (by simp [cfg0,StackProgram.initialConfig]) (by simp [cfg0,StackProgram.initialConfig]) (by simp [cfg0,StackProgram.initialConfig])
    unfold oracleMaxProgram
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [cfg0,cfg1,StackProgram.initialConfig]
  have hreverse : oracleMaxProgram.exec A cfg1 (2*x.length+1)=oracleMaxConfig .copyCount x x.reverse 0 0 := by
    have hh:=arithmeticAssemble_reverse oracleMaxTable .initCopy .initReverse .copyCount A 0 3 (by decide)
      rfl cfg1 rfl rfl x (by simp [cfg1])
    unfold oracleMaxProgram
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [cfg1,oracleMaxConfig,oracleMaxRegs]
  change oracleMaxProgram.exec A cfg0 _=_
  rw [show 9*x.length+4=(7*x.length+3)+(2*x.length+1) by omega,StackProgram.exec_add,hcopy,hreverse]

end APSCounting893.Main
end Component_23

section Component_24
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace APSCounting893.Main

lemma boundedOracleMaxAux_threshold (A : Language) (x : Word) (r fuel k result : ℕ)
    (hr : r≤k+fuel) (hresult : result=min r (k-1))
    (hA : ∀ j,j≤x.length → (A (pairWord x (encodeNat j)) ↔ j≤r))
    (hbound : k+fuel≤x.length) : boundedOracleMaxAux A x fuel k result=r := by
  classical
  induction fuel generalizing k result with
  | zero =>
    have hkr : k≤x.length := by omega
    rw [boundedOracleMaxAux]
    by_cases hle : k≤r
    · rw [if_pos ((hA k hkr).mpr hle)]
      omega
    · rw [if_neg (fun hh=>hle ((hA k hkr).mp hh)),hresult]
      omega
  | succ fuel ih =>
    rw [boundedOracleMaxAux]
    apply ih (k+1) (if A (pairWord x (encodeNat k)) then k else result)
    · omega
    · by_cases hle : k≤r
      · rw [if_pos ((hA k (by omega)).mpr hle)]
        omega
      · rw [if_neg (fun hh=>hle ((hA k (by omega)).mp hh)),hresult]
        omega
    · omega

lemma boundedOracleMaximum_threshold (A : Language) (x : Word) (r : ℕ) (hr : r≤x.length)
    (hA : ∀ j,j≤x.length → (A (pairWord x (encodeNat j)) ↔ j≤r)) :
    boundedOracleMaximum A x=r := by
  exact boundedOracleMaxAux_threshold A x r x.length 0 0 (by omega) (by simp) hA (by omega)

end APSCounting893.Main
end Component_24

section Component_25
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma boundedOracleMaximum_functionInPWithOracle (A : Language) :
    FunctionInPWithOracle A (fun x=>encodeNat (boundedOracleMaximum A x)) := by
  apply oracleMaxProgram.functionInPWithOracle A _ (.at .done .entry) 11
    (by simp [oracleMaxProgram,arithmeticAssemble,oracleMaxTable]) 200 2
  intro x
  obtain ⟨t,ht,hrun⟩:=oracleMax_loop A x x 0 0 (by simp) (by omega)
  refine ⟨(9*x.length+4)+t,?_,?_⟩
  · dsimp [polyBound]
    nlinarith
  · have hrun' : oracleMaxProgram.run A x [] ((9*x.length+4)+t)=
        oracleQueryConfig .done [] x.reverse x.length (boundedOracleMaximum A x)
          (encodeNat (boundedOracleMaximum A x)) [] [] [] := by
      rw [show oracleMaxProgram.run A x [] ((9*x.length+4)+t)=
          oracleMaxProgram.exec A (oracleMaxProgram.run A x [] (9*x.length+4)) t from
            oracleMaxProgram.exec_add A (oracleMaxProgram.initialConfig x []) (9*x.length+4) t,oracleMax_initial,hrun]
      simp [boundedOracleMaximum]
    rw [hrun']
    simp [oracleQueryConfig]

end APSCounting893.Main
end Component_25

open APSCounting893.Main
theorem solution (A : Language) :
    ∃ f : Word → Word,FunctionInPWithOracle A f ∧
      ∀ (x : Word) (r : ℕ),r≤x.length →
        (∀ j : ℕ,j≤x.length → (A (pairWord x (encodeNat j)) ↔ j≤r)) → f x=encodeNat r  := by
  refine ⟨fun x=>encodeNat (boundedOracleMaximum A x),boundedOracleMaximum_functionInPWithOracle A,?_⟩
  intro x r hr hA
  exact congrArg encodeNat (boundedOracleMaximum_threshold A x r hr hA)
