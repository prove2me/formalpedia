-- Prove2me | solution 1 for APSCounting893.Main.trailing_query_builder_correct
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:48:37.554645+00:00
-- url     : https://prove2.me/submissions/c16774f6-f884-4eba-b371-59f5a0a456bd

import Definitions.Def_APSCounting893_Main_CoefficientLanguages
import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
import Definitions.Def_APSCounting893_Main_TrailingVerifierProgram
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0
set_option autoImplicit false
namespace APSCounting893.Main

end APSCounting893.Main
end Component_0

section Component_1
set_option autoImplicit false
namespace APSCounting893.Main

end APSCounting893.Main
end Component_1

section Component_2

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
end Component_2

section Component_3

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
end Component_3

section Component_4

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
end Component_4

section Component_5

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
end Component_5

section Component_6

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
end Component_6

section Component_7
set_option autoImplicit false
namespace APSCounting893.Main
lemma assemble_copy {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r) (initial q next : Q)
    (A : Language) (src dst tmp scratch : Fin (r + 2))
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hss : src ≠ scratch)
    (hdt : dst ≠ tmp) (hds : dst ≠ scratch) (hts : tmp ≠ scratch)
    (ht : table q = .copy src dst tmp scratch next)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) (htmp : cfg.regs tmp = []) (hscratch : cfg.regs scratch = []) :
    (assemble table initial).exec A cfg (7 * w.length + 3) =
      { state := .at next .entry,
        regs := Function.update (Function.update (Function.update cfg.regs dst (w ++ cfg.regs dst)) tmp []) scratch [],
        answer := none } := by
  exact stack_copy_word_routine (assemble table initial) A src dst tmp scratch hsd hst hss hdt hds hts
    (.at q .entry) (.at q .p1) (.at q .p2) (.at q .p3) (.at q .p4) (.at q .p5)
    (.at q .p6) (.at q .p7) (.at q .p8) (.at q .p9) (.at q .p10) (.at next .entry)
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht])
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht])
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht])
    (by simp [assemble, ht]) (by simp [assemble, ht]) cfg hs ha w hw htmp hscratch

lemma assemble_encodeNat {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r) (initial q next : Q)
    (A : Language) (first second dst : Fin (r + 2)) (hfs : first ≠ second) (hfd : first ≠ dst) (hsd : second ≠ dst)
    (ht : table q = .encodeNat first second dst next)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none)
    (n : ℕ) (hfirst : cfg.regs first = n.bits.reverse) (hsecond : cfg.regs second = n.bits.reverse) :
    (assemble table initial).exec A cfg (4 * n.bits.length + 3) =
      { state := .at next .entry, regs := Function.update (Function.update (Function.update cfg.regs first []) second [])
          dst (encodeNat n ++ cfg.regs dst), answer := none } := by
  exact stack_prepend_nat_routine (assemble table initial) A first second dst hfs hfd hsd
    (.at q .entry) (.at q .p1) (.at q .p2) (.at q .p3) (.at q .p4) (.at q .p5) (.at next .entry)
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht])
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht])
    cfg hs ha n hfirst hsecond


end APSCounting893.Main
end Component_7

section Component_8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma update_empty_after_update {α : Type} [DecidableEq α] (f : α → Word) (a b : α)
    (v : Word) (hne : a ≠ b) (hb : f b = []) :
    Function.update (Function.update f a v) b [] = Function.update f a v := by
  rw [← hb, Function.update_comm hne, Function.update_eq_self]

lemma assemble_copy_clean {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r) (initial q next : Q)
    (A : Language) (src dst tmp scratch : Fin (r + 2))
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hss : src ≠ scratch)
    (hdt : dst ≠ tmp) (hds : dst ≠ scratch) (hts : tmp ≠ scratch)
    (ht : table q = .copy src dst tmp scratch next)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) (htmp : cfg.regs tmp = []) (hscratch : cfg.regs scratch = []) :
    (assemble table initial).exec A cfg (7 * w.length + 3) =
      { state := .at next .entry, regs := Function.update cfg.regs dst (w ++ cfg.regs dst), answer := none } := by
  have h := assemble_copy table initial q next A src dst tmp scratch hsd hst hss hdt hds hts ht cfg hs ha w hw htmp hscratch
  simpa only [update_empty_after_update cfg.regs dst tmp _ hdt htmp,
    update_empty_after_update cfg.regs dst scratch _ hds hscratch] using h

lemma assemble_copy2_encode {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r)
    (initial qFirst qSecond qEncode next : Q) (A : Language) (reg : Fin 6 → Fin (r + 2))
    (hinj : Function.Injective reg)
    (htFirst : table qFirst = .copy (reg 0) (reg 1) (reg 4) (reg 5) qSecond)
    (htSecond : table qSecond = .copy (reg 0) (reg 2) (reg 4) (reg 5) qEncode)
    (htEncode : table qEncode = .encodeNat (reg 1) (reg 2) (reg 3) next)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at qFirst .entry) (ha : cfg.answer = none) (n : ℕ)
    (hw : cfg.regs (reg 0) = n.bits.reverse)
    (hfirst : cfg.regs (reg 1) = []) (hsecond : cfg.regs (reg 2) = [])
    (htmp : cfg.regs (reg 4) = []) (hscratch : cfg.regs (reg 5) = []) :
    (assemble table initial).exec A cfg (18 * n.bits.length + 9) =
      { state := .at next .entry, regs := Function.update cfg.regs (reg 3) (encodeNat n ++ cfg.regs (reg 3)), answer := none } := by
  classical
  have hEq : ∀ i j : Fin 6, reg i = reg j ↔ i = j := fun i j => hinj.eq_iff
  have hne : ∀ i j : Fin 6, i ≠ j → reg i ≠ reg j := fun i j h => hinj.ne h
  let cfg1 : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r :=
    { state := .at qSecond .entry, regs := Function.update cfg.regs (reg 1) n.bits.reverse, answer := none }
  have hs1 : (assemble table initial).exec A cfg (7 * n.bits.length + 3) = cfg1 := by
    have h := assemble_copy_clean table initial qFirst qSecond A (reg 0) (reg 1) (reg 4) (reg 5)
      (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) htFirst cfg hs ha n.bits.reverse hw htmp hscratch
    simpa only [List.length_reverse, hfirst, List.append_nil] using h
  let cfg2 : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r :=
    { state := .at qEncode .entry, regs := Function.update cfg1.regs (reg 2) n.bits.reverse, answer := none }
  have hw1 : cfg1.regs (reg 0) = n.bits.reverse := by simp [cfg1, hEq, hw]
  have hsecond1 : cfg1.regs (reg 2) = [] := by simp [cfg1, hEq, hsecond]
  have htmp1 : cfg1.regs (reg 4) = [] := by simp [cfg1, hEq, htmp]
  have hscratch1 : cfg1.regs (reg 5) = [] := by simp [cfg1, hEq, hscratch]
  have hs2 : (assemble table initial).exec A cfg1 (7 * n.bits.length + 3) = cfg2 := by
    have h := assemble_copy_clean table initial qSecond qEncode A (reg 0) (reg 2) (reg 4) (reg 5)
      (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) htSecond cfg1 rfl rfl n.bits.reverse hw1 htmp1 hscratch1
    simpa only [List.length_reverse, hsecond1, List.append_nil] using h
  have hf2 : cfg2.regs (reg 1) = n.bits.reverse := by simp [cfg2, cfg1, hEq]
  have hs2bits : cfg2.regs (reg 2) = n.bits.reverse := by simp [cfg2]
  have hs3 := assemble_encodeNat table initial qEncode next A (reg 1) (reg 2) (reg 3)
    (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) htEncode cfg2 rfl rfl n hf2 hs2bits
  rw [show 18 * n.bits.length + 9 = (7 * n.bits.length + 3) + ((7 * n.bits.length + 3) + (4 * n.bits.length + 3)) by omega,
    StackProgram.exec_add, hs1, StackProgram.exec_add, hs2, hs3]
  congr 1
  funext j
  by_cases hj1 : j = reg 1
  · subst j
    simp [cfg2, cfg1, Function.update, hEq, hfirst]
  · by_cases hj2 : j = reg 2
    · subst j
      simp [cfg2, cfg1, Function.update, hEq, hsecond]
    · by_cases hj3 : j = reg 3
      · subst j
        simp [cfg2, cfg1, Function.update, hEq]
      · simp [cfg2, cfg1, Function.update, hj1, hj2, hj3]

end APSCounting893.Main
end Component_8

section Component_9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_push_word_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (dst : Fin (r + 2)) (word : Word) (label : ℕ → Q)
    (hlabel : ∀ i (hi : i < word.length), P.transition (label i) =
      .push dst (word.reverse[i]'(by simpa using hi)) (label (i + 1)))
    (cfg : StackConfig Q r) (hs : cfg.state = label 0) (ha : cfg.answer = none) :
    P.exec A cfg word.length =
      { state := label word.length, regs := Function.update cfg.regs dst (word ++ cfg.regs dst), answer := none } := by
  classical
  have hinv : ∀ t ≤ word.length, P.exec A cfg t =
      { state := label t, regs := Function.update cfg.regs dst ((word.reverse.take t).reverse ++ cfg.regs dst), answer := none } := by
    intro t ht
    induction t with
    | zero =>
        change cfg = _
        simp only [List.take_zero, List.reverse_nil, List.nil_append, Function.update_eq_self]
        cases cfg
        simp_all
    | succ t ih =>
        have ht' : t < word.length := by omega
        rw [StackProgram.exec_succ, ih (by omega)]
        simp only [StackProgram.step, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          hlabel t ht', Function.update_self]
        congr 1
        rw [List.take_succ_eq_append_getElem (by simpa using ht'), List.reverse_append,
          List.reverse_singleton, List.singleton_append, List.cons_append]
        exact Function.update_idem _ _ _
  have ht : word.reverse.take word.length = word.reverse := List.take_of_length_le (by simp)
  simpa only [ht, List.reverse_reverse] using hinv word.length le_rfl

end APSCounting893.Main
end Component_9

section Component_10
set_option autoImplicit false
namespace APSCounting893.Main
lemma assembly_constantLength_le {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r) (q : Q) :
    (table q).constantLength ≤ assemblyConstantBound table := by
  exact Finset.single_le_sum (fun q hq => Nat.zero_le (table q).constantLength) (Finset.mem_univ q)

lemma assemble_prepend {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r) (initial q next : Q)
    (A : Language) (dst : Fin (r + 2)) (word : Word) (ht : table q = .prepend dst word next)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none) :
    (assemble table initial).exec A cfg (word.length + 2) =
      { state := .at next .entry, regs := Function.update cfg.regs dst (word ++ cfg.regs dst), answer := none } := by
  let D := assemblyConstantBound table
  let label : ℕ → AssemblyControl Q D := fun i => .at q (.constant (Fin.ofNat (D + 1) i))
  have hword : word.length ≤ D := by simpa only [ht, WordOp.constantLength] using assembly_constantLength_le table q
  let cfg1 : StackConfig (AssemblyControl Q D) r := { cfg with state := label 0 }
  have hs1 : (assemble table initial).step A cfg = cfg1 := by
    simp [StackProgram.step, assemble, hs, ha, ht, cfg1, label]
  have hlabel : ∀ i (hi : i < word.length), (assemble table initial).transition (label i) =
      .push dst (word.reverse[i]'(by simpa using hi)) (label (i + 1)) := by
    intro i hi
    have hiD : i < D + 1 := by omega
    have himod : i % (assemblyConstantBound table + 1) = i := Nat.mod_eq_of_lt hiD
    simp [assemble, ht, label, himod, hi]
  have hpush := stack_push_word_routine (assemble table initial) A dst word label hlabel cfg1 rfl ha
  let cfg2 : StackConfig (AssemblyControl Q D) r :=
    { state := label word.length, regs := Function.update cfg.regs dst (word ++ cfg.regs dst), answer := none }
  have hs2 : (assemble table initial).exec A cfg1 word.length = cfg2 := hpush
  have hs3 : (assemble table initial).step A cfg2 =
      { cfg2 with state := .at next .entry } := by
    have hLD : word.length < D + 1 := by omega
    have hmod : word.length % (assemblyConstantBound table + 1) = word.length := Nat.mod_eq_of_lt hLD
    simp [StackProgram.step, assemble, ht, cfg2, label, hmod]
  rw [show word.length + 2 = 1 + (word.length + 1) by omega,
    StackProgram.exec_add, StackProgram.exec_one, hs1, StackProgram.exec_add, hs2, StackProgram.exec_one, hs3]


end APSCounting893.Main
end Component_10

section Component_11

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def trailingEncodingRegs {k : ℕ} (q : TrailingQuery)
    (source : Fin (Fintype.card (TrailingReg k) + 2)) : Fin 6 → Fin (Fintype.card (TrailingReg k) + 2) :=
  ![source, trailingRegIndex .first, trailingRegIndex .second, trailingQueryReg q,
    trailingRegIndex .copyTmp, trailingRegIndex .copyScratch]

lemma trailingEncodingRegs_bit_injective (k : ℕ) (q : TrailingQuery) :
    Function.Injective (trailingEncodingRegs q (trailingBitReg (k := k) q)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> cases q <;>
    simp_all [trailingEncodingRegs, trailingBitReg, trailingQueryReg]

lemma trailingEncodingRegs_field_injective (k : ℕ) (q : TrailingQuery) (v : Fin (k + 1)) :
    Function.Injective (trailingEncodingRegs q (trailingFieldReg q v)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> cases q <;>
    simp_all [trailingEncodingRegs, trailingFieldReg, trailingQueryReg]

lemma trailing_clean_query_update {k : ℕ} (cfg : TrailingConfig k) (hc : TrailingClean cfg)
    (q : TrailingQuery) (word : Word) (next : AssemblyControl (TrailingSite k) (assemblyConstantBound (trailingTable k)))
    (answer : Option Bool) :
    TrailingClean { state := next, regs := Function.update cfg.regs (trailingQueryReg q) word, answer := answer } := by
  cases q <;> constructor <;>
    simp_all [trailingQueryReg, hc.first, hc.second, hc.tmp, hc.scratch]

lemma trailing_build_bit {k : ℕ} (A : Language) (q : TrailingQuery) (cfg : TrailingConfig k)
    (hs : cfg.state = .at (.build q .bitFirst) .entry) (ha : cfg.answer = none)
    (hc : TrailingClean cfg) (n : ℕ) (hw : cfg.regs (trailingBitReg q) = n.bits.reverse) :
    (trailingBaseProgram k).exec A cfg (18 * n.bits.length + 9) =
      { state := .at (.build q .numerator) .entry,
        regs := Function.update cfg.regs (trailingQueryReg q) (encodeNat n ++ cfg.regs (trailingQueryReg q)), answer := none } := by
  have ht := assemble_copy2_encode (trailingTable k) .outerPair
    (.build q .bitFirst) (.build q .bitSecond) (.build q .bitEncode) (.build q .numerator) A
    (trailingEncodingRegs q (trailingBitReg q)) (trailingEncodingRegs_bit_injective k q)
    (by rfl) (by rfl) (by rfl) cfg hs ha n hw hc.first hc.second hc.tmp hc.scratch
  exact ht

lemma trailing_build_field {k : ℕ} (A : Language) (q : TrailingQuery) (i : Fin (k + 1))
    (cfg : TrailingConfig k)
    (hs : cfg.state = .at (.build q (.fieldStart ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)) .entry)
    (ha : cfg.answer = none) (hc : TrailingClean cfg) (n : ℕ)
    (hvalue : (q = .final ∧ i = Fin.last k) ∨ cfg.regs (trailingFieldReg q i) = n.bits.reverse)
    (hzero : q = .final ∧ i = Fin.last k → n = 0) :
    ∃ t ≤ 18 * n.bits.length + 9, (trailingBaseProgram k).exec A cfg t =
      { state := .at (.build q (.fieldStart ⟨i.val, by have hi := i.isLt; omega⟩)) .entry,
        regs := Function.update cfg.regs (trailingQueryReg q) (encodeNat n ++ cfg.regs (trailingQueryReg q)), answer := none } := by
  classical
  by_cases hlast : q = .final ∧ i = Fin.last k
  · have hn := hzero hlast
    subst n
    refine ⟨3, by decide, ?_⟩
    have ht := assemble_prepend (trailingTable k) .outerPair
      (.build q (.fieldStart ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))
      (.build q (.fieldStart ⟨i.val, by have hi := i.isLt; omega⟩)) A (trailingQueryReg q) (encodeNat 0)
      (by simp [trailingTable, hlast, Fin.ext_iff]) cfg hs ha
    exact ht
  · have hw : cfg.regs (trailingFieldReg q i) = n.bits.reverse := hvalue.resolve_left hlast
    refine ⟨18 * n.bits.length + 9, le_rfl, ?_⟩
    have ht := assemble_copy2_encode (trailingTable k) .outerPair
      (.build q (.fieldStart ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))
      (.build q (.fieldSecond i)) (.build q (.fieldEncode i))
      (.build q (.fieldStart ⟨i.val, by have hi := i.isLt; omega⟩)) A
      (trailingEncodingRegs q (trailingFieldReg q i)) (trailingEncodingRegs_field_injective k q i)
      (by simp [trailingTable, trailingEncodingRegs, hlast]) (by rfl) (by rfl)
      cfg hs ha n hw hc.first hc.second hc.tmp hc.scratch
    exact ht

end APSCounting893.Main
end Component_11

section Component_12
set_option autoImplicit false
namespace APSCounting893.Main
lemma assemble_jump {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r)
    (initial q next : Q) (A : Language) (ht : table q = .jump next)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none) :
    (assemble table initial).step A cfg = { cfg with state := .at next .entry } := by
  simp [StackProgram.step, hs, ha, assemble, ht]


end APSCounting893.Main
end Component_12

section Component_13

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

@[simp] lemma trailingFieldReg_ne_query {k : ℕ} (q : TrailingQuery) (i : Fin (k + 1)) :
    trailingFieldReg q i ≠ trailingQueryReg q := by
  cases q <;> simp [trailingFieldReg, trailingQueryReg]

def trailingFieldCode (f : ℕ → ℕ) : ℕ → Word
  | 0 => []
  | n + 1 => trailingFieldCode f n ++ encodeNat (f n)

lemma trailingFieldCode_eq_ofFn (f : ℕ → ℕ) (n : ℕ) :
    trailingFieldCode f n = (List.ofFn (fun i : Fin n => f i.val)).flatMap encodeNat := by
  induction n with
  | zero => simp [trailingFieldCode]
  | succ n ih =>
      rw [List.ofFn_succ']
      simpa [trailingFieldCode, List.concat_eq_append, List.flatMap_append] using
        congrArg (fun w => w ++ encodeNat (f n)) ih

lemma trailing_build_fields {k : ℕ} (A : Language) (q : TrailingQuery)
    (f : ℕ → ℕ) (B : ℕ) (n : ℕ) (hn : n ≤ k + 1) (cfg : TrailingConfig k)
    (hs : cfg.state = .at (.build q (.fieldStart ⟨n, by omega⟩)) .entry)
    (ha : cfg.answer = none) (hc : TrailingClean cfg)
    (hvalue : ∀ i : Fin (k + 1), (q = .final ∧ i = Fin.last k) ∨
      cfg.regs (trailingFieldReg q i) = (f i.val).bits.reverse)
    (hzero : q = .final → f k = 0)
    (hB : ∀ i < n, (f i).bits.length ≤ B) :
    ∃ t ≤ 1 + n * (18 * B + 9), (trailingBaseProgram k).exec A cfg t =
      { state := .at (.build q .countPrefix) .entry,
        regs := Function.update cfg.regs (trailingQueryReg q)
          (trailingFieldCode f n ++ cfg.regs (trailingQueryReg q)), answer := none } := by
  classical
  induction n generalizing cfg with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      have ht := assemble_jump (trailingTable k) .outerPair
        (.build q (.fieldStart ⟨0, by omega⟩)) (.build q .countPrefix) A
        (by simp [trailingTable]) cfg hs ha
      simpa only [trailingBaseProgram, StackProgram.exec_one, trailingFieldCode, List.nil_append,
        Function.update_eq_self, ha] using ht
  | succ n ih =>
      let i : Fin (k + 1) := ⟨n, by omega⟩
      obtain ⟨t, ht, he⟩ := trailing_build_field A q i cfg hs ha hc (f n) (hvalue i)
        (by intro h; have hv := congrArg Fin.val h.2; change n = k at hv; simpa [hv] using hzero h.1)
      let cfg1 : TrailingConfig k :=
        { state := .at (.build q (.fieldStart ⟨n, by omega⟩)) .entry,
          regs := Function.update cfg.regs (trailingQueryReg q)
            (encodeNat (f n) ++ cfg.regs (trailingQueryReg q)), answer := none }
      have he1 : (trailingBaseProgram k).exec A cfg t = cfg1 := he
      have hc1 : TrailingClean cfg1 := trailing_clean_query_update cfg hc q _ _ _
      have hv1 : ∀ j : Fin (k + 1), (q = .final ∧ j = Fin.last k) ∨
          cfg1.regs (trailingFieldReg q j) = (f j.val).bits.reverse := by
        intro j
        simpa only [cfg1, Function.update_of_ne (trailingFieldReg_ne_query q j)] using hvalue j
      obtain ⟨s, hsB, he2⟩ := ih (by omega) cfg1 rfl rfl hc1 hv1
        (fun j hj => hB j (by omega))
      refine ⟨t + s, ?_, ?_⟩
      · have hb := hB n (by omega)
        calc
          t + s ≤ (18 * (f n).bits.length + 9) + (1 + n * (18 * B + 9)) := Nat.add_le_add ht hsB
          _ ≤ 1 + (n + 1) * (18 * B + 9) := by nlinarith
      · rw [StackProgram.exec_add, he1, he2]
        simp only [cfg1, trailingFieldCode, Function.update_self,
          Function.update_idem, List.append_assoc]

end APSCounting893.Main
end Component_13

section Component_14

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma trailing_build_query {k : ℕ} (A : Language) (q : TrailingQuery) (cfg : TrailingConfig k)
    (hs : cfg.state = .at (.build q .bitFirst) .entry) (ha : cfg.answer = none)
    (hc : TrailingClean cfg) (x : Word) (e : Fin (k + 1) →₀ ℕ) (bitIndex B : ℕ)
    (hbit : cfg.regs (trailingBitReg q) = bitIndex.bits.reverse)
    (hfields : ∀ i : Fin (k + 1), (q = .final ∧ i = Fin.last k) ∨
      cfg.regs (trailingFieldReg q i) = (e i).bits.reverse)
    (hzero : q = .final → e (Fin.last k) = 0)
    (hB : ∀ i, (e i).bits.length ≤ B)
    (hp : cfg.regs (trailingRegIndex .inputPrefix) = encodeNat x.length ++ x)
    (hq : cfg.regs (trailingQueryReg q) = []) :
    ∃ t ≤ 18 * bitIndex.bits.length + 9 + 4 + (1 + (k + 1) * (18 * B + 9)) +
        (encodeNat (k + 1)).length + 2 + 7 * (encodeNat x.length ++ x).length + 3,
      (trailingBaseProgram k).exec A cfg t =
        { state := .at (trailingAfterBuild k q) .entry,
          regs := Function.update cfg.regs (trailingQueryReg q)
            (coefficientQuery x e .numerator bitIndex), answer := none } := by
  classical
  let C : TrailingBuildPhase k → Word → TrailingConfig k := fun site word =>
    { state := .at (.build q site) .entry,
      regs := Function.update cfg.regs (trailingQueryReg q) word, answer := none }
  have hclean (site : TrailingBuildPhase k) (word : Word) : TrailingClean (C site word) :=
    trailing_clean_query_update cfg hc q word _ _
  have hfield (site : TrailingBuildPhase k) (word : Word) (i : Fin (k + 1)) :
      (C site word).regs (trailingFieldReg q i) = cfg.regs (trailingFieldReg q i) := by
    simp only [C, Function.update_of_ne (trailingFieldReg_ne_query q i)]
  have hprefix (site : TrailingBuildPhase k) (word : Word) :
      (C site word).regs (trailingRegIndex .inputPrefix) = encodeNat x.length ++ x := by
    cases q <;> simpa [C, trailingQueryReg] using hp
  let w1 := encodeNat bitIndex
  let w2 := [false, true] ++ w1
  have he1 : (trailingBaseProgram k).exec A cfg (18 * bitIndex.bits.length + 9) = C .numerator w1 := by
    simpa only [hq, List.append_nil] using trailing_build_bit A q cfg hs ha hc bitIndex hbit
  have he2 : (trailingBaseProgram k).exec A (C .numerator w1) 4 =
      C (.fieldStart ⟨k + 1, by omega⟩) w2 := by
    have hh := assemble_prepend (trailingTable k) .outerPair (.build q .numerator)
      (.build q (.fieldStart ⟨k + 1, by omega⟩)) A (trailingQueryReg q) [false, true]
      (by rfl) (C .numerator w1) rfl rfl
    simpa only [trailingBaseProgram, C, w2, Function.update_self, Function.update_idem, List.length_cons, List.length_nil] using hh
  let f : ℕ → ℕ := fun j => if h : j < k + 1 then e ⟨j, h⟩ else 0
  have hf (i : Fin (k + 1)) : f i.val = e i := by simp only [f, dif_pos i.isLt]
  have hvalues : ∀ i : Fin (k + 1), (q = .final ∧ i = Fin.last k) ∨
      (C (.fieldStart ⟨k + 1, by omega⟩) w2).regs (trailingFieldReg q i) = (f i.val).bits.reverse := by
    intro i
    simpa only [hfield, hf] using hfields i
  obtain ⟨tf, htf, hef⟩ := trailing_build_fields A q f B (k + 1) le_rfl
    (C (.fieldStart ⟨k + 1, by omega⟩) w2) rfl rfl (hclean _ _) hvalues
    (by intro h; simpa [f, Fin.last] using hzero h)
    (by intro i hi; simpa only [f, dif_pos hi] using hB ⟨i, hi⟩)
  have hcode : trailingFieldCode f (k + 1) = (List.ofFn (fun i => e i)).flatMap encodeNat := by
    rw [trailingFieldCode_eq_ofFn]
    have hh : List.ofFn (fun i : Fin (k + 1) => f i.val) = List.ofFn (fun i => e i) := by
      congr 1
      funext i
      exact hf i
    rw [hh]
  let w3 := (List.ofFn (fun i => e i)).flatMap encodeNat ++ w2
  have he3 : (trailingBaseProgram k).exec A (C (.fieldStart ⟨k + 1, by omega⟩) w2) tf =
      C .countPrefix w3 := by
    simpa only [C, Function.update_self, Function.update_idem, hcode] using hef
  let w4 := encodeNat (k + 1) ++ w3
  have he4 : (trailingBaseProgram k).exec A (C .countPrefix w3) ((encodeNat (k + 1)).length + 2) =
      C .inputPrefix w4 := by
    have hh := assemble_prepend (trailingTable k) .outerPair (.build q .countPrefix)
      (.build q .inputPrefix) A (trailingQueryReg q) (encodeNat (k + 1))
      (by rfl) (C .countPrefix w3) rfl rfl
    simpa only [trailingBaseProgram, C, w4, Function.update_self, Function.update_idem] using hh
  have he5 := assemble_copy_clean (trailingTable k) .outerPair (.build q .inputPrefix)
    (trailingAfterBuild k q) A (trailingRegIndex .inputPrefix) (trailingQueryReg q)
    (trailingRegIndex .copyTmp) (trailingRegIndex .copyScratch)
    (by cases q <;> simp [trailingQueryReg]) (by simp) (by simp)
    (by cases q <;> simp [trailingQueryReg]) (by cases q <;> simp [trailingQueryReg]) (by simp)
    (by rfl) (C .inputPrefix w4) rfl rfl (encodeNat x.length ++ x) (hprefix _ _)
    (hclean _ _).tmp (hclean _ _).scratch
  refine ⟨(18 * bitIndex.bits.length + 9) + 4 + tf + ((encodeNat (k + 1)).length + 2) +
      (7 * (encodeNat x.length ++ x).length + 3), by omega, ?_⟩
  have h12 : (trailingBaseProgram k).exec A cfg ((18 * bitIndex.bits.length + 9) + 4) =
      C (.fieldStart ⟨k + 1, by omega⟩) w2 := by rw [StackProgram.exec_add, he1, he2]
  have h123 : (trailingBaseProgram k).exec A cfg ((18 * bitIndex.bits.length + 9) + 4 + tf) =
      C .countPrefix w3 := by rw [StackProgram.exec_add, h12, he3]
  have h1234 : (trailingBaseProgram k).exec A cfg
      ((18 * bitIndex.bits.length + 9) + 4 + tf + ((encodeNat (k + 1)).length + 2)) =
      C .inputPrefix w4 := by rw [StackProgram.exec_add, h123, he4]
  rw [StackProgram.exec_add, h1234]
  unfold trailingBaseProgram
  rw [he5]
  simp only [C, Function.update_self, Function.update_idem]
  have hword : encodeNat x.length ++ x ++ w4 = coefficientQuery x e .numerator bitIndex := by
    simp [w4, w3, w2, w1, coefficientQuery, encodeList, CoefficientPart.encode, List.append_assoc]
  rw [hword]

end APSCounting893.Main
end Component_14

open APSCounting893.Main
theorem solution {k : ℕ} (A : Language) (q : TrailingQuery) (cfg : TrailingConfig k)
    (hs : cfg.state = .at (.build q .bitFirst) .entry) (ha : cfg.answer = none)
    (hc : TrailingClean cfg) (x : Word) (e : Fin (k + 1) →₀ ℕ) (bitIndex B : ℕ)
    (hbit : cfg.regs (trailingBitReg q) = bitIndex.bits.reverse)
    (hfields : ∀ i : Fin (k + 1), (q = .final ∧ i = Fin.last k) ∨
      cfg.regs (trailingFieldReg q i) = (e i).bits.reverse)
    (hzero : q = .final → e (Fin.last k) = 0)
    (hB : ∀ i, (e i).bits.length ≤ B)
    (hp : cfg.regs (trailingRegIndex .inputPrefix) = encodeNat x.length ++ x)
    (hq : cfg.regs (trailingQueryReg q) = []) :
    ∃ t ≤ 18 * bitIndex.bits.length + 9 + 4 + (1 + (k + 1) * (18 * B + 9)) +
        (encodeNat (k + 1)).length + 2 + 7 * (encodeNat x.length ++ x).length + 3,
      (trailingBaseProgram k).exec A cfg t =
        { state := .at (trailingAfterBuild k q) .entry,
          regs := Function.update cfg.regs (trailingQueryReg q)
            (coefficientQuery x e .numerator bitIndex), answer := none } := by
  exact APSCounting893.Main.trailing_build_query A q cfg hs ha hc x e bitIndex B hbit hfields hzero hB hp hq
