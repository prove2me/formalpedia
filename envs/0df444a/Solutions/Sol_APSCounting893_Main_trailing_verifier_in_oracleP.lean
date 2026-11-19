-- Prove2me | solution 1 for APSCounting893.Main.trailing_verifier_in_oracleP
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:48:38.038066+00:00
-- url     : https://prove2.me/submissions/f66d3895-410e-4625-8ff4-3178595e6758

import Definitions.Def_APSCounting893_Main_CoefficientLanguages
import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
import Definitions.Def_APSCounting893_Main_TrailingVerifierProgram
import Theorems.Thm_APSCounting893_Main_stack_program_polynomial_simulation
import Theorems.Thm_APSCounting893_Main_trailing_query_builder_correct
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0
set_option autoImplicit false
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
  exact trailing_query_builder_correct A q cfg hs ha hc x e bitIndex B hbit hfields hzero hB hp hq

end APSCounting893.Main
end Component_0

section Component_1
set_option autoImplicit false
namespace APSCounting893.Main

end APSCounting893.Main
end Component_1

section Component_2
set_option autoImplicit false
namespace APSCounting893.Main

end APSCounting893.Main
end Component_2

section Component_3

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
end Component_3

section Component_4

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
end Component_4

section Component_5

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
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma decodePair_pairWord (x y : Word) : decodePair (pairWord x y) = some (x, y) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
      change (decodePair (pairWord x y)).map _ = _
      rw [ih]
      rfl

lemma stack_pair_parser_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src dst : Fin (r + 2)) (hne : src ≠ dst) (loop value zero one finish fail : Q)
    (hloop : P.transition loop = .pop src finish value fail)
    (hvalue : P.transition value = .pop src zero one fail)
    (hzero : P.transition zero = .push dst false loop)
    (hone : P.transition one = .push dst true loop)
    (cfg : StackConfig Q r) (hs : cfg.state = loop) (ha : cfg.answer = none)
    (x y : Word) (hw : cfg.regs src = pairWord x y) :
    P.exec A cfg (3 * x.length + 1) =
      { state := finish,
        regs := Function.update (Function.update cfg.regs src y) dst (x.reverse ++ cfg.regs dst),
        answer := none } := by
  classical
  induction x generalizing cfg with
  | nil =>
      change P.step A cfg = _
      have hs1 : P.step A cfg = { state := finish, regs := Function.update cfg.regs src y, answer := none } := by
        simp [StackProgram.step, hs, ha, hloop, hw, pairWord]
      rw [hs1]
      congr 1
      funext j
      by_cases hjd : j = dst
      · subst j; simp [hne, Ne.symm hne]
      · simp [Function.update, hjd]
  | cons b x ih =>
      let next := if b then one else zero
      let cfg1 : StackConfig Q r :=
        { state := value, regs := Function.update cfg.regs src (b :: pairWord x y), answer := none }
      let cfg2 : StackConfig Q r :=
        { state := next, regs := Function.update cfg.regs src (pairWord x y), answer := none }
      let cfg3 : StackConfig Q r :=
        { state := loop, regs := (Function.update (Function.update cfg.regs src (pairWord x y)) dst
          (b :: cfg.regs dst)), answer := none }
      have hstep1 : P.step A cfg = cfg1 := by
        simp [StackProgram.step, hs, ha, hloop, hw, pairWord, cfg1]
      have hstep2 : P.step A cfg1 = cfg2 := by
        cases b <;> simp [StackProgram.step, cfg1, cfg2, hvalue, next]
      have hstep3 : P.step A cfg2 = cfg3 := by
        cases b <;> simp [StackProgram.step, cfg2, cfg3, next, hzero, hone, Ne.symm hne]
      have hsrc : cfg3.regs src = pairWord x y := by simp [cfg3, hne]
      have hrec := ih cfg3 rfl rfl hsrc
      rw [show 3 * (b :: x).length + 1 = 1 + (1 + (1 + (3 * x.length + 1))) by simp; omega,
        StackProgram.exec_add, StackProgram.exec_one, hstep1,
        StackProgram.exec_add, StackProgram.exec_one, hstep2,
        StackProgram.exec_add, StackProgram.exec_one, hstep3, hrec]
      congr 1
      funext j
      by_cases hjs : j = src
      · subst j
        simp [cfg3, Function.update, hne, Ne.symm hne]
      · by_cases hjd : j = dst
        · subst j
          simp [cfg3, Function.update, hne, Ne.symm hne, List.reverse_cons, List.append_assoc]
        · simp [cfg3, Function.update, hjs, hjd]

lemma decodePair_inverse (v x y : Word) (h : decodePair v = some (x, y)) : v = pairWord x y := by
  induction v using List.twoStepInduction generalizing x y with
  | nil => simp [decodePair] at h
  | singleton b =>
      cases b with
      | false =>
          have heq : ([], []) = (x, y) := by simpa [decodePair] using h
          cases heq
          rfl
      | true => simp [decodePair] at h
  | cons_cons b c v ih _ =>
      cases b with
      | false =>
          have heq : ([], c :: v) = (x, y) := by simpa [decodePair] using h
          cases heq
          rfl
      | true =>
          cases hv : decodePair v with
          | none => simp [decodePair, hv] at h
          | some p =>
              have heq : (c :: p.1, p.2) = (x, y) := by simpa [decodePair, hv] using h
              cases heq
              rw [ih p.1 p.2 hv]
              rfl

lemma stack_pair_parser_failure {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src dst : Fin (r + 2)) (hne : src ≠ dst) (loop value zero one finish fail : Q)
    (hloop : P.transition loop = .pop src finish value fail)
    (hvalue : P.transition value = .pop src zero one fail)
    (hzero : P.transition zero = .push dst false loop)
    (hone : P.transition one = .push dst true loop)
    (cfg : StackConfig Q r) (hs : cfg.state = loop) (ha : cfg.answer = none)
    (v : Word) (hw : cfg.regs src = v) (hv : decodePair v = none) :
    ∃ t ≤ 3 * v.length + 2, (P.exec A cfg t).state = fail ∧ (P.exec A cfg t).answer = none := by
  classical
  induction v using List.twoStepInduction generalizing cfg with
  | nil =>
      refine ⟨1, by simp, ?_⟩
      change (P.step A cfg).state = fail ∧ (P.step A cfg).answer = none
      simp [StackProgram.step, hs, ha, hloop, hw]
  | singleton b =>
      cases b with
      | false => simp [decodePair] at hv
      | true =>
          refine ⟨2, by simp, ?_⟩
          change (P.step A (P.step A cfg)).state = fail ∧ (P.step A (P.step A cfg)).answer = none
          simp [StackProgram.step, hs, ha, hloop, hvalue, hw]
  | cons_cons b c v ih _ =>
      cases b with
      | false => simp [decodePair] at hv
      | true =>
          have hv' : decodePair v = none := by
            cases hdec : decodePair v <;> simp [decodePair, hdec] at hv ⊢
          let next := if c then one else zero
          let cfg1 : StackConfig Q r :=
            { state := value, regs := Function.update cfg.regs src (c :: v), answer := none }
          let cfg2 : StackConfig Q r :=
            { state := next, regs := Function.update cfg.regs src v, answer := none }
          let cfg3 : StackConfig Q r :=
            { state := loop, regs := Function.update (Function.update cfg.regs src v) dst
                (c :: cfg.regs dst), answer := none }
          have hs1 : P.step A cfg = cfg1 := by
            simp [StackProgram.step, hs, ha, hloop, hw, cfg1]
          have hs2 : P.step A cfg1 = cfg2 := by
            cases c <;> simp [StackProgram.step, cfg1, cfg2, hvalue, next]
          have hs3 : P.step A cfg2 = cfg3 := by
            cases c <;> simp [StackProgram.step, cfg2, cfg3, next, hzero, hone, Ne.symm hne]
          have hw3 : cfg3.regs src = v := by simp [cfg3, hne]
          obtain ⟨t, ht, hst, hans⟩ := ih cfg3 rfl rfl hw3 hv'
          refine ⟨1 + (1 + (1 + t)), by simp only [List.length_cons]; omega, ?_⟩
          rw [StackProgram.exec_add, StackProgram.exec_one, hs1,
            StackProgram.exec_add, StackProgram.exec_one, hs2,
            StackProgram.exec_add, StackProgram.exec_one, hs3]
          exact ⟨hst, hans⟩

end APSCounting893.Main
end Component_7

section Component_8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_unary_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src counter : Fin (r + 2)) (hne : src ≠ counter) (loop save finish fail : Q)
    (hloop : P.transition loop = .pop src finish save fail)
    (hsave : P.transition save = .push counter true loop)
    (cfg : StackConfig Q r) (hs : cfg.state = loop) (ha : cfg.answer = none)
    (k : ℕ) (rest : Word) (hw : cfg.regs src = List.replicate k true ++ false :: rest) :
    P.exec A cfg (2 * k + 1) =
      { state := finish,
        regs := Function.update (Function.update cfg.regs src rest) counter (List.replicate k true ++ cfg.regs counter),
        answer := none } := by
  classical
  induction k generalizing cfg with
  | zero =>
      change P.step A cfg = _
      have hs1 : P.step A cfg = { state := finish, regs := Function.update cfg.regs src rest, answer := none } := by
        simp [StackProgram.step, hs, ha, hloop, hw]
      rw [hs1]
      congr 1
      funext j
      by_cases hj : j = counter
      · subst j; simp [hne, Ne.symm hne]
      · simp [Function.update, hj]
  | succ k ih =>
      let cfg1 : StackConfig Q r :=
        { state := save, regs := Function.update cfg.regs src (List.replicate k true ++ false :: rest), answer := none }
      let cfg2 : StackConfig Q r :=
        { state := loop, regs := Function.update (Function.update cfg.regs src (List.replicate k true ++ false :: rest))
            counter (true :: cfg.regs counter), answer := none }
      have hs1 : P.step A cfg = cfg1 := by
        simp [StackProgram.step, hs, ha, hloop, hw, List.replicate_succ, cfg1]
      have hs2 : P.step A cfg1 = cfg2 := by
        simp [StackProgram.step, hsave, cfg1, cfg2, Ne.symm hne]
      have hsrc : cfg2.regs src = List.replicate k true ++ false :: rest := by simp [cfg2, hne]
      have hrec := ih cfg2 rfl rfl hsrc
      rw [show 2 * (k + 1) + 1 = 1 + (1 + (2 * k + 1)) by omega,
        StackProgram.exec_add, StackProgram.exec_one, hs1,
        StackProgram.exec_add, StackProgram.exec_one, hs2, hrec]
      congr 1
      funext j
      by_cases hjs : j = src
      · subst j; simp [cfg2, Function.update, hne, Ne.symm hne]
      · by_cases hjc : j = counter
        · subst j
          simp [cfg2, Function.update, hne, Ne.symm hne, List.replicate_succ', List.append_assoc]
        · simp [cfg2, Function.update, hjs, hjc]

lemma stack_unary_missing_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src counter : Fin (r + 2)) (hne : src ≠ counter) (loop save finish fail : Q)
    (hloop : P.transition loop = .pop src finish save fail)
    (hsave : P.transition save = .push counter true loop)
    (cfg : StackConfig Q r) (hs : cfg.state = loop) (ha : cfg.answer = none)
    (k : ℕ) (hw : cfg.regs src = List.replicate k true) :
    P.exec A cfg (2 * k + 1) =
      { state := fail,
        regs := Function.update (Function.update cfg.regs src []) counter (List.replicate k true ++ cfg.regs counter),
        answer := none } := by
  classical
  induction k generalizing cfg with
  | zero =>
      change P.step A cfg = _
      have hs1 : P.step A cfg = { state := fail, regs := Function.update cfg.regs src [], answer := none } := by
        simp [StackProgram.step, hs, ha, hloop, hw]
      rw [hs1]
      congr 1
      funext j
      by_cases hj : j = counter
      · subst j; simp [hne, Ne.symm hne]
      · simp [Function.update, hj]
  | succ k ih =>
      let cfg1 : StackConfig Q r :=
        { state := save, regs := Function.update cfg.regs src (List.replicate k true), answer := none }
      let cfg2 : StackConfig Q r :=
        { state := loop, regs := Function.update (Function.update cfg.regs src (List.replicate k true))
            counter (true :: cfg.regs counter), answer := none }
      have hs1 : P.step A cfg = cfg1 := by
        simp [StackProgram.step, hs, ha, hloop, hw, List.replicate_succ, cfg1]
      have hs2 : P.step A cfg1 = cfg2 := by
        simp [StackProgram.step, hsave, cfg1, cfg2, Ne.symm hne]
      have hsrc : cfg2.regs src = List.replicate k true := by simp [cfg2, hne]
      have hrec := ih cfg2 rfl rfl hsrc
      rw [show 2 * (k + 1) + 1 = 1 + (1 + (2 * k + 1)) by omega,
        StackProgram.exec_add, StackProgram.exec_one, hs1,
        StackProgram.exec_add, StackProgram.exec_one, hs2, hrec]
      congr 1
      funext j
      by_cases hjs : j = src
      · subst j; simp [cfg2, Function.update, hne, Ne.symm hne]
      · by_cases hjc : j = counter
        · subst j
          simp [cfg2, Function.update, hne, Ne.symm hne, List.replicate_succ', List.append_assoc]
        · simp [cfg2, Function.update, hjs, hjc]

end APSCounting893.Main
end Component_8

section Component_9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_fixed_bits_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src counter dst : Fin (r + 2)) (hsc : src ≠ counter) (hsd : src ≠ dst) (hcd : counter ≠ dst)
    (loop value zero one finish fail : Q)
    (hloop : P.transition loop = .pop counter value value finish)
    (hvalue : P.transition value = .pop src zero one fail)
    (hzero : P.transition zero = .push dst false loop)
    (hone : P.transition one = .push dst true loop)
    (cfg : StackConfig Q r) (hs : cfg.state = loop) (ha : cfg.answer = none)
    (bits rest : Word) (hw : cfg.regs src = bits ++ rest)
    (hc : cfg.regs counter = List.replicate bits.length true) :
    P.exec A cfg (3 * bits.length + 1) =
      { state := finish,
        regs := Function.update (Function.update (Function.update cfg.regs src rest) counter [])
          dst (bits.reverse ++ cfg.regs dst), answer := none } := by
  classical
  induction bits generalizing cfg with
  | nil =>
      change P.step A cfg = _
      have hup : Function.update cfg.regs src rest = cfg.regs := by
        simpa only [List.nil_append] using congrArg (Function.update cfg.regs src) hw.symm |>.trans
          (Function.update_eq_self src cfg.regs)
      have huc : Function.update cfg.regs counter [] = cfg.regs := by
        rw [show ([] : Word) = cfg.regs counter by simpa using hc.symm]
        exact Function.update_eq_self counter cfg.regs
      simp [StackProgram.step, hs, ha, hloop, hc, hup, huc]
  | cons b bits ih =>
      let cfg1 : StackConfig Q r :=
        { state := value, regs := Function.update cfg.regs counter (List.replicate bits.length true), answer := none }
      let next := if b then one else zero
      let cfg2 : StackConfig Q r :=
        { state := next, regs := Function.update cfg1.regs src (bits ++ rest), answer := none }
      let cfg3 : StackConfig Q r :=
        { state := loop, regs := Function.update cfg2.regs dst (b :: cfg.regs dst), answer := none }
      have hs1 : P.step A cfg = cfg1 := by
        simp [StackProgram.step, hs, ha, hloop, hc, List.replicate_succ, cfg1]
      have hs2 : P.step A cfg1 = cfg2 := by
        cases b <;> simp [StackProgram.step, cfg1, cfg2, hvalue, hw, hsc, next]
      have hs3 : P.step A cfg2 = cfg3 := by
        cases b <;> simp [StackProgram.step, cfg2, cfg3, cfg1, next, hzero, hone, Ne.symm hsd, Ne.symm hcd]
      have hw3 : cfg3.regs src = bits ++ rest := by simp [cfg3, cfg2, hsd]
      have hc3 : cfg3.regs counter = List.replicate bits.length true := by simp [cfg3, cfg2, cfg1, hcd, Ne.symm hsc]
      have hrec := ih cfg3 rfl rfl hw3 hc3
      rw [show 3 * (b :: bits).length + 1 = 1 + (1 + (1 + (3 * bits.length + 1))) by simp; omega,
        StackProgram.exec_add, StackProgram.exec_one, hs1,
        StackProgram.exec_add, StackProgram.exec_one, hs2,
        StackProgram.exec_add, StackProgram.exec_one, hs3, hrec]
      congr 1
      funext j
      by_cases hjs : j = src
      · subst j
        simp [cfg3, cfg2, cfg1, Function.update, hsc, hsd, Ne.symm hsc, Ne.symm hsd]
      · by_cases hjc : j = counter
        · subst j
          simp [cfg3, cfg2, cfg1, Function.update, hcd, Ne.symm hcd, Ne.symm hsc]
        · by_cases hjd : j = dst
          · subst j
            simp [cfg3, cfg2, cfg1, Function.update, Ne.symm hsd, Ne.symm hcd,
              List.reverse_cons, List.append_assoc]
          · simp [cfg3, cfg2, cfg1, Function.update, hjs, hjc, hjd]

end APSCounting893.Main
end Component_9

section Component_10

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
end Component_10

section Component_11

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
end Component_11

section Component_12

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
namespace APSCounting893.Main

lemma readUnary_code (k : ℕ) (rest : Word) :
    readUnary (List.replicate k true ++ false :: rest) = some (k, rest) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append, readUnary, ih, Option.map_some]

lemma readUnary_inverse (w : Word) (k : ℕ) (rest : Word) (h : readUnary w = some (k, rest)) :
    w = List.replicate k true ++ false :: rest := by
  induction w generalizing k rest with
  | nil => simp [readUnary] at h
  | cons b w ih =>
      cases b with
      | false =>
          have heq : (0, w) = (k, rest) := by simpa [readUnary] using h
          cases heq
          rfl
      | true =>
          cases hw : readUnary w with
          | none => simp [readUnary, hw] at h
          | some p =>
              have heq : (p.1 + 1, p.2) = (k, rest) := by simpa [readUnary, hw] using h
              obtain ⟨hk, hr⟩ := Prod.mk.inj heq
              subst k
              rw [← hr, ih p.1 p.2 hw]
              simp [List.replicate_succ]

lemma decodeNat_code (n : ℕ) (rest : Word) : decodeNat (encodeNat n ++ rest) = some (n, rest) := by
  have hw : encodeNat n ++ rest = List.replicate n.bits.length true ++ false :: (n.bits ++ rest) := by
    simp [encodeNat, List.append_assoc]
  rw [hw]
  simp [decodeNat, readUnary_code, List.take_left, canonicalBits_nat_bits, bitsValue, nat_bits_fold]

lemma decodeNat_inverse (w : Word) (n : ℕ) (rest : Word) (h : decodeNat w = some (n, rest)) :
    w = encodeNat n ++ rest := by
  cases hu : readUnary w with
  | none => simp [decodeNat, hu] at h
  | some p =>
      have hw := readUnary_inverse w p.1 p.2 hu
      by_cases hlen : p.1 ≤ p.2.length
      · by_cases hc : canonicalBits (p.2.take p.1) = true
        · have heq : (bitsValue (p.2.take p.1), p.2.drop p.1) = (n, rest) := by
            simpa [decodeNat, hu, hlen, hc] using h
          obtain ⟨hn, hr⟩ := Prod.mk.inj heq
          have hb : n.bits = p.2.take p.1 := by rw [← hn]; exact bitsValue_bits_of_canonical _ hc
          have hk : n.bits.length = p.1 := by rw [hb, List.length_take, Nat.min_eq_left hlen]
          rw [hw]
          simp only [encodeNat, hk]
          rw [hb, ← hr]
          simp [List.append_assoc]
        · simp [decodeNat, hu, hlen, hc] at h
      · simp [decodeNat, hu, hlen] at h

lemma readUnary_none_iff (w : Word) : readUnary w = none ↔ w = List.replicate w.length true := by
  induction w with
  | nil => simp [readUnary]
  | cons b w ih =>
      cases b with
      | false => simp [readUnary, List.replicate_succ]
      | true => simpa [readUnary, List.replicate_succ] using ih

lemma readUnary_length (w : Word) (k : ℕ) (rest : Word) (h : readUnary w = some (k, rest)) :
    w.length = k + 1 + rest.length := by
  rw [readUnary_inverse w k rest h]
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end APSCounting893.Main
end Component_12

section Component_13

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_truncated_bits_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src counter dst : Fin (r + 2)) (hsc : src ≠ counter) (hsd : src ≠ dst) (hcd : counter ≠ dst)
    (loop value zero one finish fail : Q)
    (hloop : P.transition loop = .pop counter value value finish)
    (hvalue : P.transition value = .pop src zero one fail)
    (hzero : P.transition zero = .push dst false loop)
    (hone : P.transition one = .push dst true loop)
    (cfg : StackConfig Q r) (hs : cfg.state = loop) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) (k : ℕ) (hc : cfg.regs counter = List.replicate k true)
    (hk : w.length < k) :
    (P.exec A cfg (3 * w.length + 2)).state = fail ∧
      (P.exec A cfg (3 * w.length + 2)).answer = none := by
  classical
  induction w generalizing cfg k with
  | nil =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simpa using Nat.ne_of_gt hk)
      change (P.step A (P.step A cfg)).state = fail ∧ (P.step A (P.step A cfg)).answer = none
      simp [StackProgram.step, hs, ha, hloop, hvalue, hw, hc, List.replicate_succ, hsc]
  | cons b w ih =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      let cfg1 : StackConfig Q r :=
        { state := value, regs := Function.update cfg.regs counter (List.replicate k true), answer := none }
      let next := if b then one else zero
      let cfg2 : StackConfig Q r :=
        { state := next, regs := Function.update cfg1.regs src w, answer := none }
      let cfg3 : StackConfig Q r :=
        { state := loop, regs := Function.update cfg2.regs dst (b :: cfg.regs dst), answer := none }
      have hs1 : P.step A cfg = cfg1 := by
        simp [StackProgram.step, hs, ha, hloop, hc, List.replicate_succ, cfg1]
      have hs2 : P.step A cfg1 = cfg2 := by
        cases b <;> simp [StackProgram.step, cfg1, cfg2, hvalue, hw, hsc, next]
      have hs3 : P.step A cfg2 = cfg3 := by
        cases b <;> simp [StackProgram.step, cfg2, cfg3, cfg1, next, hzero, hone, Ne.symm hsd, Ne.symm hcd]
      have hw3 : cfg3.regs src = w := by simp [cfg3, cfg2, hsd]
      have hc3 : cfg3.regs counter = List.replicate k true := by simp [cfg3, cfg2, cfg1, hcd, Ne.symm hsc]
      have hrec := ih cfg3 rfl rfl hw3 k hc3 (by simp only [List.length_cons] at hk; omega)
      rw [show 3 * (b :: w).length + 2 = 1 + (1 + (1 + (3 * w.length + 2))) by simp; omega,
        StackProgram.exec_add, StackProgram.exec_one, hs1,
        StackProgram.exec_add, StackProgram.exec_one, hs2,
        StackProgram.exec_add, StackProgram.exec_one, hs3]
      exact hrec

end APSCounting893.Main
end Component_13

section Component_14

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_binary_field_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src counter dst : Fin (r + 2)) (hsc : src ≠ counter) (hsd : src ≠ dst) (hcd : counter ≠ dst)
    (unary save bitsLoop value zero one check finish fail : Q)
    (hunary : P.transition unary = .pop src bitsLoop save fail)
    (hsave : P.transition save = .push counter true unary)
    (hbits : P.transition bitsLoop = .pop counter value value check)
    (hvalue : P.transition value = .pop src zero one fail)
    (hzero : P.transition zero = .push dst false bitsLoop)
    (hone : P.transition one = .push dst true bitsLoop)
    (hcheck : P.transition check = .peek dst fail finish finish)
    (cfg : StackConfig Q r) (hs : cfg.state = unary) (ha : cfg.answer = none)
    (bits : Word) (rest : Word) (hw : cfg.regs src = List.replicate bits.length true ++ false :: (bits ++ rest))
    (hc : cfg.regs counter = []) (hd : cfg.regs dst = []) :
    P.exec A cfg (5 * bits.length + 3) =
      { state := if canonicalBits bits then finish else fail,
        regs := Function.update (Function.update (Function.update cfg.regs src rest) counter []) dst bits.reverse,
        answer := none } := by
  classical
  let cfg1 : StackConfig Q r :=
    { state := bitsLoop,
      regs := Function.update (Function.update cfg.regs src (bits ++ rest)) counter (List.replicate bits.length true),
      answer := none }
  have hs1 : P.exec A cfg (2 * bits.length + 1) = cfg1 := by
    have ht := stack_unary_routine P A src counter hsc unary save bitsLoop fail hunary hsave cfg hs ha
      bits.length (bits ++ rest) hw
    simpa only [hc, List.append_nil] using ht
  let cfg2 : StackConfig Q r :=
    { state := check,
      regs := Function.update (Function.update (Function.update cfg.regs src rest) counter []) dst bits.reverse,
      answer := none }
  have hw1 : cfg1.regs src = bits ++ rest := by simp [cfg1, hsc]
  have hc1 : cfg1.regs counter = List.replicate bits.length true := by simp [cfg1]
  have hd1 : cfg1.regs dst = [] := by simp [cfg1, Ne.symm hsd, Ne.symm hcd, hd]
  have hs2 : P.exec A cfg1 (3 * bits.length + 1) = cfg2 := by
    rw [stack_fixed_bits_routine P A src counter dst hsc hsd hcd bitsLoop value zero one check fail
      hbits hvalue hzero hone cfg1 rfl rfl bits rest hw1 hc1]
    congr 1
    funext j
    by_cases hjs : j = src
    · subst j; simp [cfg2, cfg1, Function.update, hsc, hsd, Ne.symm hsc, Ne.symm hsd]
    · by_cases hjc : j = counter
      · subst j; simp [cfg2, cfg1, Function.update, hcd, Ne.symm hcd]
      · by_cases hjd : j = dst
        · subst j; simp [cfg2, cfg1, Function.update, Ne.symm hsd, Ne.symm hcd, hd]
        · simp [cfg2, cfg1, Function.update, hjs, hjc, hjd]
  have hs3 : P.step A cfg2 = { cfg2 with state := if canonicalBits bits then finish else fail } := by
    have hh := canonicalBits_eq_reverse_headD bits
    cases hb : bits.reverse with
    | nil =>
        have hcanon : canonicalBits bits = true := by rw [hh, hb]; rfl
        simp [StackProgram.step, cfg2, hcheck, hb, hcanon]
    | cons b w =>
        have hcanon : canonicalBits bits = b := by rw [hh, hb]; rfl
        cases b <;> simp [StackProgram.step, cfg2, hcheck, hb, hcanon]
  rw [show 5 * bits.length + 3 = (2 * bits.length + 1) + ((3 * bits.length + 1) + 1) by omega,
    StackProgram.exec_add, hs1, StackProgram.exec_add, hs2, StackProgram.exec_one, hs3]

lemma stack_nat_parser_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src counter dst : Fin (r + 2)) (hsc : src ≠ counter) (hsd : src ≠ dst) (hcd : counter ≠ dst)
    (unary save bitsLoop value zero one check finish fail : Q)
    (hunary : P.transition unary = .pop src bitsLoop save fail)
    (hsave : P.transition save = .push counter true unary)
    (hbits : P.transition bitsLoop = .pop counter value value check)
    (hvalue : P.transition value = .pop src zero one fail)
    (hzero : P.transition zero = .push dst false bitsLoop)
    (hone : P.transition one = .push dst true bitsLoop)
    (hcheck : P.transition check = .peek dst fail finish finish)
    (cfg : StackConfig Q r) (hs : cfg.state = unary) (ha : cfg.answer = none)
    (n : ℕ) (rest : Word) (hw : cfg.regs src = encodeNat n ++ rest)
    (hc : cfg.regs counter = []) (hd : cfg.regs dst = []) :
    P.exec A cfg (5 * n.bits.length + 3) =
      { state := finish,
        regs := Function.update (Function.update (Function.update cfg.regs src rest) counter []) dst n.bits.reverse,
        answer := none } := by
  have hinput : cfg.regs src = List.replicate n.bits.length true ++ false :: (n.bits ++ rest) := by
    rw [hw]
    simp [encodeNat, List.append_assoc]
  have ht := stack_binary_field_routine P A src counter dst hsc hsd hcd unary save bitsLoop value zero one check finish fail
    hunary hsave hbits hvalue hzero hone hcheck cfg hs ha n.bits rest hinput hc hd
  simpa only [canonicalBits_nat_bits, ↓reduceIte] using ht

lemma stack_nat_parser_terminates {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src counter dst : Fin (r + 2)) (hsc : src ≠ counter) (hsd : src ≠ dst) (hcd : counter ≠ dst)
    (unary save bitsLoop value zero one check finish fail : Q)
    (hunary : P.transition unary = .pop src bitsLoop save fail)
    (hsave : P.transition save = .push counter true unary)
    (hbits : P.transition bitsLoop = .pop counter value value check)
    (hvalue : P.transition value = .pop src zero one fail)
    (hzero : P.transition zero = .push dst false bitsLoop)
    (hone : P.transition one = .push dst true bitsLoop)
    (hcheck : P.transition check = .peek dst fail finish finish)
    (cfg : StackConfig Q r) (hs : cfg.state = unary) (ha : cfg.answer = none)
    (v : Word) (hw : cfg.regs src = v) (hc : cfg.regs counter = []) (hd : cfg.regs dst = []) :
    ∃ t ≤ 5 * v.length + 3, (P.exec A cfg t).answer = none ∧
      ((P.exec A cfg t).state = finish ∨ (P.exec A cfg t).state = fail) := by
  classical
  cases hu : readUnary v with
  | none =>
      have hraw := (readUnary_none_iff v).mp hu
      have ht := stack_unary_missing_routine P A src counter hsc unary save bitsLoop fail
        hunary hsave cfg hs ha v.length (hw.trans hraw)
      refine ⟨2 * v.length + 1, by omega, ?_⟩
      rw [ht]
      exact ⟨rfl, Or.inr rfl⟩
  | some p =>
      rcases p with ⟨k, rest⟩
      have hraw := readUnary_inverse v k rest hu
      have hvlen := readUnary_length v k rest hu
      have hinput := hw.trans hraw
      by_cases hlen : k ≤ rest.length
      · have hbitslen : (rest.take k).length = k := by simp [List.length_take, Nat.min_eq_left hlen]
        have hinput' : cfg.regs src = List.replicate (rest.take k).length true ++
            false :: ((rest.take k) ++ rest.drop k) := by
          rw [hbitslen, List.take_append_drop]
          exact hinput
        have ht := stack_binary_field_routine P A src counter dst hsc hsd hcd unary save bitsLoop value zero one check finish fail
          hunary hsave hbits hvalue hzero hone hcheck cfg hs ha (rest.take k) (rest.drop k) hinput' hc hd
        refine ⟨5 * (rest.take k).length + 3, by omega, ?_⟩
        rw [ht]
        refine ⟨rfl, ?_⟩
        by_cases hcan : canonicalBits (rest.take k) = true <;> simp [hcan]
      · let cfg1 : StackConfig Q r :=
          { state := bitsLoop,
            regs := Function.update (Function.update cfg.regs src rest) counter (List.replicate k true), answer := none }
        have ht1 : P.exec A cfg (2 * k + 1) = cfg1 := by
          have ht := stack_unary_routine P A src counter hsc unary save bitsLoop fail hunary hsave cfg hs ha k rest hinput
          simpa only [hc, List.append_nil] using ht
        have hw1 : cfg1.regs src = rest := by simp [cfg1, hsc]
        have hc1 : cfg1.regs counter = List.replicate k true := by simp [cfg1]
        have ht2 := stack_truncated_bits_routine P A src counter dst hsc hsd hcd bitsLoop value zero one check fail
          hbits hvalue hzero hone cfg1 rfl rfl rest hw1 k hc1 (by omega)
        refine ⟨(2 * k + 1) + (3 * rest.length + 2), by omega, ?_⟩
        rw [StackProgram.exec_add, ht1]
        exact ⟨ht2.2, Or.inr ht2.1⟩

end APSCounting893.Main
end Component_14

section Component_15

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
end Component_15

section Component_16

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
end Component_16

section Component_17

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
end Component_17

section Component_18

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
namespace APSCounting893.Main

lemma bitsValue_append (x y : Word) :
    bitsValue (x ++ y) = bitsValue x + 2 ^ x.length * bitsValue y := by
  induction x with
  | nil => simp [bitsValue]
  | cons b x ih =>
      cases b <;> simp only [List.cons_append, bitsValue, List.foldr_cons, Nat.bit_val,
        List.length_cons, pow_succ] at ih ⊢ <;> nlinarith

def msbValue (w : Word) : ℕ := bitsValue w.reverse

lemma msbValue_cons (b : Bool) (w : Word) :
    msbValue (b :: w) = b.toNat * 2 ^ w.length + msbValue w := by
  simp only [msbValue, List.reverse_cons, bitsValue_append, List.length_reverse]
  cases b <;> simp [bitsValue, Nat.bit_val, Nat.add_comm, Nat.mul_comm]

lemma msbValue_lt_pow (w : Word) : msbValue w < 2 ^ w.length := by
  induction w with
  | nil => decide
  | cons b w ih =>
      rw [msbValue_cons]
      cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, zero_mul, one_mul,
        zero_add, List.length_cons, pow_succ] <;> omega

lemma msb_lex_iff_lt (x y : Word) (hlen : x.length = y.length) :
    List.Lex (· < ·) x y ↔ msbValue x < msbValue y := by
  induction x generalizing y with
  | nil =>
      have hy : y = [] := List.length_eq_zero_iff.mp hlen.symm
      subst y
      simp [msbValue, bitsValue]
  | cons b x ih =>
      cases y with
      | nil => simp at hlen
      | cons c y =>
          have ht : x.length = y.length := Nat.succ.inj hlen
          have hx := msbValue_lt_pow x
          have hy := msbValue_lt_pow y
          have hh := ih y ht
          rw [List.cons_lex_cons_iff, msbValue_cons, msbValue_cons]
          rw [ht] at hx
          have htf : ¬ (true : Bool) < false := by decide
          cases b <;> cases c <;> simp [htf, ht, hh] <;> omega


lemma nat_bits_length_lt_implies_lt (n m : ℕ) (h : n.bits.length < m.bits.length) : n < m := by
  by_contra hn
  have hs := Nat.size_le_size (Nat.le_of_not_gt hn)
  rw [← Nat.size_eq_bits_len, ← Nat.size_eq_bits_len] at hs
  omega

lemma nat_lt_iff_bits_length_lex (n m : ℕ) :
    n < m ↔ n.bits.length < m.bits.length ∨
      (n.bits.length = m.bits.length ∧ List.Lex (· < ·) n.bits.reverse m.bits.reverse) := by
  have hvn : msbValue n.bits.reverse = n := by simp only [msbValue, List.reverse_reverse, bitsValue, nat_bits_fold]
  have hvm : msbValue m.bits.reverse = m := by simp only [msbValue, List.reverse_reverse, bitsValue, nat_bits_fold]
  constructor
  · intro h
    have hlen : n.bits.length ≤ m.bits.length := by
      simpa only [← Nat.size_eq_bits_len] using Nat.size_le_size h.le
    obtain hlt | heq := lt_or_eq_of_le hlen
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, (msb_lex_iff_lt _ _ (by simpa using heq)).mpr (by rwa [hvn, hvm])⟩
  · rintro (hlen | ⟨hlen, hlex⟩)
    · exact nat_bits_length_lt_implies_lt n m hlen
    · have h := (msb_lex_iff_lt _ _ (by simpa using hlen)).mp hlex
      rwa [hvn, hvm] at h

end APSCounting893.Main
end Component_18

section Component_19

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main

def wordCompare : Word → Word → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | b :: x, c :: y => if b = c then wordCompare x y else if b then .gt else .lt

lemma wordCompare_lt_iff (x y : Word) : wordCompare x y = .lt ↔ List.Lex (· < ·) x y := by
  have htf : ¬ (true : Bool) < false := by decide
  induction x generalizing y with
  | nil => cases y <;> simp [wordCompare]
  | cons b x ih =>
      cases y with
      | nil => simp [wordCompare]
      | cons c y => cases b <;> cases c <;> simp [wordCompare, List.cons_lex_cons_iff, htf, ih]

lemma wordCompare_eq_iff (x y : Word) : wordCompare x y = .eq ↔ x = y := by
  induction x generalizing y with
  | nil => cases y <;> simp [wordCompare]
  | cons b x ih =>
      cases y with
      | nil => simp [wordCompare]
      | cons c y => cases b <;> cases c <;> simp [wordCompare, ih]

lemma wordCompare_gt_iff (x y : Word) : wordCompare x y = .gt ↔ List.Lex (· < ·) y x := by
  have htf : ¬ (true : Bool) < false := by decide
  induction x generalizing y with
  | nil => cases y <;> simp [wordCompare]
  | cons b x ih =>
      cases y with
      | nil => simp [wordCompare]
      | cons c y => cases b <;> cases c <;> simp [wordCompare, List.cons_lex_cons_iff, htf, ih]

end APSCounting893.Main
end Component_19

section Component_20

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def comparisonState {Q : Type} (less equal greater : Q) : Ordering → Q
  | .lt => less | .eq => equal | .gt => greater

lemma stack_word_compare_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (left right : Fin (r + 2)) (hne : left ≠ right) (loop zero one empty less equal greater : Q)
    (hloop : P.transition loop = .pop left zero one empty)
    (hzero : P.transition zero = .pop right loop less greater)
    (hone : P.transition one = .pop right greater loop greater)
    (hempty : P.transition empty = .pop right less less equal)
    (cfg : StackConfig Q r) (hs : cfg.state = loop) (ha : cfg.answer = none)
    (x y : Word) (hx : cfg.regs left = x) (hy : cfg.regs right = y) :
    ∃ t ≤ 2 * (min x.length y.length + 1),
      (P.exec A cfg t).state = comparisonState less equal greater (wordCompare x y) ∧
      (P.exec A cfg t).answer = none ∧
      ∀ j, j ≠ left → j ≠ right → (P.exec A cfg t).regs j = cfg.regs j := by
  classical
  induction x generalizing cfg y with
  | nil =>
      refine ⟨2, by simp, ?_⟩
      change (P.step A (P.step A cfg)).state = _ ∧ (P.step A (P.step A cfg)).answer = none ∧
              ∀ j, j ≠ left → j ≠ right → (P.step A (P.step A cfg)).regs j = cfg.regs j
      cases y with
      | nil => simp [StackProgram.step, hs, ha, hloop, hempty, hx, hy, Ne.symm hne, wordCompare, comparisonState, Function.update] <;> intro j hjl hjr <;> simp [hjl, hjr]
      | cons b y => cases b <;> simp [StackProgram.step, hs, ha, hloop, hempty, hx, hy,
          Ne.symm hne, wordCompare, comparisonState, Function.update] <;> intro j hjl hjr <;> simp [hjl, hjr]
  | cons b x ih =>
      cases y with
      | nil =>
          refine ⟨2, by simp, ?_⟩
          change (P.step A (P.step A cfg)).state = _ ∧ (P.step A (P.step A cfg)).answer = none ∧
              ∀ j, j ≠ left → j ≠ right → (P.step A (P.step A cfg)).regs j = cfg.regs j
          cases b <;> simp [StackProgram.step, hs, ha, hloop, hzero, hone, hx, hy,
            Ne.symm hne, wordCompare, comparisonState, Function.update] <;> intro j hjl hjr <;> simp [hjl, hjr]
      | cons c y =>
          let first := if b then one else zero
          let next := if b = c then loop else if b then greater else less
          let cfg1 : StackConfig Q r :=
            { state := first, regs := Function.update cfg.regs left x, answer := none }
          let cfg2 : StackConfig Q r :=
            { state := next, regs := Function.update (Function.update cfg.regs left x) right y, answer := none }
          have hs1 : P.step A cfg = cfg1 := by
            cases b <;> simp [StackProgram.step, hs, ha, hloop, hx, cfg1, first]
          have hs2 : P.step A cfg1 = cfg2 := by
            cases b <;> cases c <;> simp [StackProgram.step, hzero, hone, cfg1, cfg2, hy, Ne.symm hne, first, next]
          have hmin : min (b :: x).length (c :: y).length = min x.length y.length + 1 := by
            simp only [List.length_cons]; omega
          by_cases hbc : b = c
          · subst c
            have hstate : cfg2.state = loop := by simp [cfg2, next]
            have hx2 : cfg2.regs left = x := by simp [cfg2, hne]
            have hy2 : cfg2.regs right = y := by simp [cfg2]
            obtain ⟨t, ht, hst, hans, hregs⟩ := ih cfg2 hstate rfl y hx2 hy2
            have hexeq : P.exec A cfg (2 + t) = P.exec A cfg2 t := by
              rw [show 2 + t = 1 + (1 + t) by omega, StackProgram.exec_add, StackProgram.exec_one, hs1,
                StackProgram.exec_add, StackProgram.exec_one, hs2]
            refine ⟨2 + t, by omega, ?_⟩
            rw [hexeq]
            refine ⟨by simpa [wordCompare] using hst, hans, ?_⟩
            intro j hjl hjr
            rw [hregs j hjl hjr]
            simp [cfg2, Function.update, hjl, hjr]
          · refine ⟨2, by omega, ?_⟩
            change (P.step A (P.step A cfg)).state = _ ∧ (P.step A (P.step A cfg)).answer = none ∧
              ∀ j, j ≠ left → j ≠ right → (P.step A (P.step A cfg)).regs j = cfg.regs j
            rw [hs1, hs2]
            cases b <;> cases c <;> simp_all [cfg2, next, wordCompare, comparisonState, Function.update] <;> intro j hjl hjr <;> simp [hjl, hjr]

end APSCounting893.Main
end Component_20

section Component_21

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_length_compare_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (left right : Fin (r + 2)) (hne : left ≠ right) (loop hasLeft emptyLeft less equal greater : Q)
    (hloop : P.transition loop = .pop left hasLeft hasLeft emptyLeft)
    (hhas : P.transition hasLeft = .pop right loop loop greater)
    (hempty : P.transition emptyLeft = .pop right less less equal)
    (cfg : StackConfig Q r) (hs : cfg.state = loop) (ha : cfg.answer = none)
    (x y : Word) (hx : cfg.regs left = x) (hy : cfg.regs right = y) :
    P.exec A cfg (2 * min x.length y.length + 2) =
      { state := if x.length < y.length then less else if y.length < x.length then greater else equal,
        regs := Function.update (Function.update cfg.regs left (x.drop (min x.length y.length + 1))) right
          (y.drop (min x.length y.length + 1)), answer := none } := by
  classical
  induction x generalizing cfg y with
  | nil =>
      cases y with
      | nil =>
          change P.step A (P.step A cfg) = _
          simp [StackProgram.step, hs, ha, hloop, hempty, hx, hy, Ne.symm hne]
      | cons b y =>
          change P.step A (P.step A cfg) = _
          cases b <;> simp [StackProgram.step, hs, ha, hloop, hempty, hx, hy, Ne.symm hne]
  | cons b x ih =>
      cases y with
      | nil =>
          change P.step A (P.step A cfg) = _
          cases b <;> simp [StackProgram.step, hs, ha, hloop, hhas, hx, hy, Ne.symm hne]
      | cons c y =>
          let cfg1 : StackConfig Q r :=
            { state := hasLeft, regs := Function.update cfg.regs left x, answer := none }
          let cfg2 : StackConfig Q r :=
            { state := loop, regs := Function.update (Function.update cfg.regs left x) right y, answer := none }
          have hs1 : P.step A cfg = cfg1 := by
            cases b <;> simp [StackProgram.step, hs, ha, hloop, hx, cfg1]
          have hs2 : P.step A cfg1 = cfg2 := by
            cases c <;> simp [StackProgram.step, hhas, cfg1, cfg2, hy, Ne.symm hne]
          have hx2 : cfg2.regs left = x := by simp [cfg2, hne]
          have hy2 : cfg2.regs right = y := by simp [cfg2]
          have hrec := ih cfg2 rfl rfl y hx2 hy2
          have hmin : min (b :: x).length (c :: y).length = min x.length y.length + 1 := by
            simp only [List.length_cons]
            omega
          rw [hmin, show 2 * (min x.length y.length + 1) + 2 =
              1 + (1 + (2 * min x.length y.length + 2)) by omega,
            StackProgram.exec_add, StackProgram.exec_one, hs1,
            StackProgram.exec_add, StackProgram.exec_one, hs2, hrec]
          simp only [List.length_cons, Nat.add_lt_add_iff_right, List.drop_succ_cons]
          congr 1
          funext j
          by_cases hjl : j = left
          · subst j; simp [cfg2, Function.update, hne, Ne.symm hne]
          · by_cases hjr : j = right
            · subst j; simp [cfg2, Function.update, hne, Ne.symm hne]
            · simp [cfg2, Function.update, hjl, hjr]

end APSCounting893.Main
end Component_21

section Component_22

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma assemble_reverse {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r) (initial q next : Q)
    (A : Language) (src dst : Fin (r + 2)) (hne : src ≠ dst)
    (ht : table q = .reverse src dst next)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none) (w : Word) (hw : cfg.regs src = w) :
    (assemble table initial).exec A cfg (2 * w.length + 1) =
      { state := .at next .entry, regs := Function.update (Function.update cfg.regs src []) dst
          (w.reverse ++ cfg.regs dst), answer := none } := by
  apply stack_reverse_routine (assemble table initial) A src dst hne (.at q .entry) (.at q .p1) (.at q .p2) (.at next .entry)
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht]) cfg hs ha w hw

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

lemma assemble_pair {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r) (initial q next : Q)
    (A : Language) (src dst : Fin (r + 2)) (hne : src ≠ dst) (failure : Bool)
    (ht : table q = .pair src dst next failure)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none)
    (x y : Word) (hw : cfg.regs src = pairWord x y) :
    (assemble table initial).exec A cfg (3 * x.length + 1) =
      { state := .at next .entry,
        regs := Function.update (Function.update cfg.regs src y) dst (x.reverse ++ cfg.regs dst), answer := none } := by
  exact stack_pair_parser_routine (assemble table initial) A src dst hne
    (.at q .entry) (.at q .p1) (.at q .p2) (.at q .p3) (.at next .entry) (.halt failure)
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht])
    cfg hs ha x y hw

lemma assemble_nat {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r) (initial q next : Q)
    (A : Language) (src counter dst : Fin (r + 2)) (hsc : src ≠ counter) (hsd : src ≠ dst) (hcd : counter ≠ dst)
    (failure : Bool) (ht : table q = .nat src counter dst next failure)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none)
    (n : ℕ) (rest : Word) (hw : cfg.regs src = encodeNat n ++ rest)
    (hc : cfg.regs counter = []) (hd : cfg.regs dst = []) :
    (assemble table initial).exec A cfg (5 * n.bits.length + 3) =
      { state := .at next .entry, regs := Function.update (Function.update (Function.update cfg.regs src rest) counter [])
          dst n.bits.reverse, answer := none } := by
  exact stack_nat_parser_routine (assemble table initial) A src counter dst hsc hsd hcd
    (.at q .entry) (.at q .p1) (.at q .p2) (.at q .p3) (.at q .p4) (.at q .p5) (.at q .p6)
    (.at next .entry) (.halt failure)
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht])
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht])
    cfg hs ha n rest hw hc hd

lemma assemble_length {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r) (initial q next : Q)
    (A : Language) (src counter tmp : Fin (r + 2)) (hsc : src ≠ counter) (hst : src ≠ tmp) (hct : counter ≠ tmp)
    (ht : table q = .length src counter tmp next)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) (n : ℕ) (hn : cfg.regs counter = n.bits) (htmp : cfg.regs tmp = []) :
    (assemble table initial).exec A cfg (lengthCountTime n w.length) =
      { state := .at next .entry, regs := Function.update (Function.update (Function.update cfg.regs src [])
          counter (n + w.length).bits) tmp [], answer := none } := by
  exact stack_length_routine (assemble table initial) A src counter tmp hsc hst hct
    (.at q .entry) (.at q .p1) (.at q .p2) (.at q .p3) (.at q .p4) (.at q .p5) (.at q .p6) (.at next .entry)
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht])
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht])
    cfg hs ha w hw n hn htmp

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
end Component_22

section Component_23

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
end Component_23

section Component_24

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
end Component_24

section Component_25

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def stripWord : Word → Word → Option Word
  | [], input => some input
  | b :: word, c :: input => if b = c then stripWord word input else none
  | _ :: _, [] => none

lemma stripWord_prefix (word rest : Word) : stripWord word (word ++ rest) = some rest := by
  induction word with
  | nil => rfl
  | cons b word ih => simpa [stripWord] using ih

lemma stack_check_word_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src : Fin (r + 2)) (word : Word) (label : ℕ → Q) (fail : Q)
    (hlabel : ∀ i (hi : i < word.length), P.transition (label i) = .pop src
      (if word[i] then fail else label (i + 1)) (if word[i] then label (i + 1) else fail) fail)
    (cfg : StackConfig Q r) (hs : cfg.state = label 0) (ha : cfg.answer = none)
    (input : Word) (hw : cfg.regs src = input) :
    ∃ t ≤ word.length, (P.exec A cfg t).answer = none ∧
      match stripWord word input with
      | none => (P.exec A cfg t).state = fail
      | some rest => (P.exec A cfg t).state = label word.length ∧
          (P.exec A cfg t).regs = Function.update cfg.regs src rest := by
  classical
  induction word generalizing cfg label input with
  | nil =>
      refine ⟨0, by simp, ?_⟩
      change cfg.answer = none ∧ cfg.state = label 0 ∧ cfg.regs = Function.update cfg.regs src input
      refine ⟨ha, hs, ?_⟩
      rw [← hw]
      exact (Function.update_eq_self src cfg.regs).symm
  | cons b word ih =>
      have h0 := hlabel 0 (by simp)
      simp only [List.getElem_cons_zero, zero_add] at h0
      cases input with
      | nil =>
          refine ⟨1, by simp, ?_⟩
          change (P.step A cfg).answer = none ∧ (P.step A cfg).state = fail
          simp [StackProgram.step, hs, ha, h0, hw]
      | cons c input =>
          by_cases hbc : b = c
          · subst c
            let cfg1 : StackConfig Q r :=
              { state := label 1, regs := Function.update cfg.regs src input, answer := none }
            have hs1 : P.step A cfg = cfg1 := by
              cases b <;> simp [StackProgram.step, hs, ha, h0, hw, cfg1]
            let nextLabel : ℕ → Q := fun i => label (i + 1)
            have hl : ∀ i (hi : i < word.length), P.transition (nextLabel i) = .pop src
                (if word[i] then fail else nextLabel (i + 1)) (if word[i] then nextLabel (i + 1) else fail) fail := by
              intro i hi
              have hn := hlabel (i + 1) (by simpa using hi)
              change P.transition (label (i + 1)) = .pop src
                (if word[i] then fail else label (i + 1 + 1))
                (if word[i] then label (i + 1 + 1) else fail) fail at hn
              simpa only [nextLabel, Nat.add_assoc] using hn
            have hw1 : cfg1.regs src = input := by simp [cfg1]
            obtain ⟨t, ht, hans, hresult⟩ := ih nextLabel hl cfg1 rfl rfl input hw1
            have hexeq : P.exec A cfg (1 + t) = P.exec A cfg1 t := by
              rw [StackProgram.exec_add, StackProgram.exec_one, hs1]
            refine ⟨1 + t, by simp only [List.length_cons]; omega, ?_⟩
            rw [hexeq]
            refine ⟨hans, ?_⟩
            simp only [stripWord, if_pos rfl, ite_true]
            cases hp : stripWord word input with
            | none => simpa only [hp] using hresult
            | some rest =>
                rw [hp] at hresult
                refine ⟨hresult.1, ?_⟩
                rw [hresult.2]
                exact Function.update_idem _ _ _
          · refine ⟨1, by simp, ?_⟩
            rw [show stripWord (b :: word) (c :: input) = none by simp [stripWord, hbc]]
            change (P.step A cfg).answer = none ∧ (P.step A cfg).state = fail
            cases b <;> cases c <;> simp_all [StackProgram.step]

end APSCounting893.Main
end Component_25

section Component_26

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
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

lemma assemble_check {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r) (initial q next : Q)
    (A : Language) (src : Fin (r + 2)) (word : Word) (failure : Bool)
    (ht : table q = .check src word next failure)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none) (input : Word) (hw : cfg.regs src = input) :
    ∃ t ≤ word.length + 2, ((assemble table initial).exec A cfg t).answer = none ∧
      match stripWord word input with
      | none => ((assemble table initial).exec A cfg t).state = .halt failure
      | some rest => ((assemble table initial).exec A cfg t).state = .at next .entry ∧
          ((assemble table initial).exec A cfg t).regs = Function.update cfg.regs src rest := by
  classical
  let D := assemblyConstantBound table
  let label : ℕ → AssemblyControl Q D := fun i => .at q (.constant (Fin.ofNat (D + 1) i))
  have hword : word.length ≤ D := by simpa only [ht, WordOp.constantLength] using assembly_constantLength_le table q
  let cfg1 : StackConfig (AssemblyControl Q D) r := { cfg with state := label 0 }
  have hs1 : (assemble table initial).step A cfg = cfg1 := by
    simp [StackProgram.step, assemble, hs, ha, ht, cfg1, label]
  have hlabel : ∀ i (hi : i < word.length), (assemble table initial).transition (label i) = .pop src
      (if word[i] then .halt failure else label (i + 1))
      (if word[i] then label (i + 1) else .halt failure) (.halt failure) := by
    intro i hi
    have hiD : i < D + 1 := by omega
    have himod : i % (assemblyConstantBound table + 1) = i := Nat.mod_eq_of_lt hiD
    simp [assemble, ht, label, himod, hi]
  obtain ⟨t, htime, hans, hresult⟩ := stack_check_word_routine (assemble table initial) A src word label (.halt failure)
    hlabel cfg1 rfl ha input hw
  have hexeq : (assemble table initial).exec A cfg (1 + t) = (assemble table initial).exec A cfg1 t := by
    rw [StackProgram.exec_add, StackProgram.exec_one, hs1]
  cases hp : stripWord word input with
  | none =>
      refine ⟨1 + t, by omega, ?_⟩
      rw [hexeq]
      exact ⟨hans, by simpa only [hp] using hresult⟩
  | some rest =>
      rw [hp] at hresult
      have hLD : word.length < D + 1 := by omega
      have hmod : word.length % (assemblyConstantBound table + 1) = word.length := Nat.mod_eq_of_lt hLD
      have hstate := hresult.1
      have hregs : ((assemble table initial).exec A cfg1 t).regs = Function.update cfg.regs src rest := hresult.2
      have htransition : (assemble table initial).transition (((assemble table initial).exec A cfg1 t).state) =
          .jump (.at next .entry) := by
        rw [hstate]
        simp [assemble, ht, label, hmod]
      have hsfinal : (assemble table initial).step A ((assemble table initial).exec A cfg1 t) =
          { state := .at next .entry, regs := Function.update cfg.regs src rest, answer := none } := by
        simp only [StackProgram.step, hans, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, htransition, hregs]
      refine ⟨(1 + t) + 1, by omega, ?_⟩
      rw [StackProgram.exec_succ, hexeq, hsfinal]
      exact ⟨rfl, rfl, rfl⟩

end APSCounting893.Main
end Component_26

section Component_27
set_option autoImplicit false
namespace APSCounting893.Main
lemma trailing_clean_query_update {k : ℕ} (cfg : TrailingConfig k) (hc : TrailingClean cfg)
    (q : TrailingQuery) (word : Word) (next : AssemblyControl (TrailingSite k) (assemblyConstantBound (trailingTable k)))
    (answer : Option Bool) :
    TrailingClean { state := next, regs := Function.update cfg.regs (trailingQueryReg q) word, answer := answer } := by
  cases q <;> constructor <;>
    simp_all [trailingQueryReg, hc.first, hc.second, hc.tmp, hc.scratch]


end APSCounting893.Main
end Component_27

section Component_28

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def trailingLengthEncodingRegs (k : ℕ) : Fin 6 → Fin (Fintype.card (TrailingReg k) + 2) :=
  ![trailingRegIndex .lengthMSB, trailingRegIndex .first, trailingRegIndex .second,
    trailingRegIndex .inputPrefix, trailingRegIndex .copyTmp, trailingRegIndex .copyScratch]

lemma trailingLengthEncodingRegs_injective (k : ℕ) : Function.Injective (trailingLengthEncodingRegs k) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [trailingLengthEncodingRegs]

lemma trailing_input_prefix {k : ℕ} (A : Language) (cfg : TrailingConfig k)
    (hs : cfg.state = .at .copyXForLength .entry) (ha : cfg.answer = none)
    (hc : TrailingClean cfg) (x : Word) (hx : cfg.regs (trailingRegIndex .x) = x)
    (hl : cfg.regs (trailingRegIndex .lengthLSB) = [])
    (hm : cfg.regs (trailingRegIndex .lengthMSB) = [])
    (hp : cfg.regs (trailingRegIndex .inputPrefix) = []) :
    (trailingBaseProgram k).exec A cfg
      ((7 * x.length + 3) + lengthCountTime 0 x.length + (2 * x.length.bits.length + 1) +
        (7 * x.length + 3) + (18 * x.length.bits.length + 9)) =
      { state := .at (.build .candidate .bitFirst) .entry,
        regs := Function.update (Function.update cfg.regs (trailingRegIndex .lengthMSB) x.length.bits.reverse)
          (trailingRegIndex .inputPrefix) (encodeNat x.length ++ x), answer := none } := by
  classical
  let C1 : TrailingConfig k :=
    { state := .at .lengthX .entry, regs := Function.update cfg.regs (trailingRegIndex .first) x, answer := none }
  have h1 : (trailingBaseProgram k).exec A cfg (7 * x.length + 3) = C1 := by
    have hh := assemble_copy_clean (trailingTable k) .outerPair .copyXForLength .lengthX A
      (trailingRegIndex .x) (trailingRegIndex .first) (trailingRegIndex .copyTmp) (trailingRegIndex .copyScratch)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by rfl) cfg hs ha x hx hc.tmp hc.scratch
    simpa only [trailingBaseProgram, C1, hc.first, List.append_nil] using hh
  let C2 : TrailingConfig k :=
    { state := .at .reverseLength .entry,
      regs := Function.update cfg.regs (trailingRegIndex .lengthLSB) x.length.bits, answer := none }
  have h2 : (trailingBaseProgram k).exec A C1 (lengthCountTime 0 x.length) = C2 := by
    have hh := assemble_length (trailingTable k) .outerPair .lengthX .reverseLength A
      (trailingRegIndex .first) (trailingRegIndex .lengthLSB) (trailingRegIndex .second)
      (by simp) (by simp) (by simp) (by rfl) C1 rfl rfl x
      (by simp [C1]) 0 (by simp [C1, hl]) (by simp [C1, hc.second])
    simp only [C1, Function.update_idem, Nat.zero_add] at hh
    rw [show Function.update cfg.regs (trailingRegIndex .first) [] = cfg.regs from
        by rw [← hc.first]; exact Function.update_eq_self _ _,
      update_empty_after_update cfg.regs (trailingRegIndex .lengthLSB) (trailingRegIndex .second)
        _ (by simp) hc.second] at hh
    simpa only [trailingBaseProgram, C1, C2] using hh
  let C3 : TrailingConfig k :=
    { state := .at .copyXPrefix .entry,
      regs := Function.update cfg.regs (trailingRegIndex .lengthMSB) x.length.bits.reverse, answer := none }
  have h3 : (trailingBaseProgram k).exec A C2 (2 * x.length.bits.length + 1) = C3 := by
    have hh := assemble_reverse (trailingTable k) .outerPair .reverseLength .copyXPrefix A
      (trailingRegIndex .lengthLSB) (trailingRegIndex .lengthMSB) (by simp) (by rfl)
      C2 rfl rfl x.length.bits (by simp [C2])
    simp only [C2, Function.update_idem] at hh
    rw [show Function.update cfg.regs (trailingRegIndex .lengthLSB) [] = cfg.regs from
      by rw [← hl]; exact Function.update_eq_self _ _] at hh
    simpa only [trailingBaseProgram, C2, C3, Function.update_of_ne
      (by simp : trailingRegIndex (k := k) .lengthMSB ≠ trailingRegIndex .lengthLSB),
      hm, List.append_nil] using hh
  let C4 : TrailingConfig k :=
    { state := .at .copyLengthFirst .entry,
      regs := Function.update C3.regs (trailingRegIndex .inputPrefix) x, answer := none }
  have h4 : (trailingBaseProgram k).exec A C3 (7 * x.length + 3) = C4 := by
    have hh := assemble_copy_clean (trailingTable k) .outerPair .copyXPrefix .copyLengthFirst A
      (trailingRegIndex .x) (trailingRegIndex .inputPrefix) (trailingRegIndex .copyTmp) (trailingRegIndex .copyScratch)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by rfl) C3 rfl rfl x
      (by simpa [C3] using hx) (by simpa [C3] using hc.tmp) (by simpa [C3] using hc.scratch)
    simpa only [trailingBaseProgram, C3, Function.update_of_ne
      (by simp : trailingRegIndex (k := k) .inputPrefix ≠ trailingRegIndex .lengthMSB), hp, List.append_nil] using hh
  have h5 := assemble_copy2_encode (trailingTable k) .outerPair .copyLengthFirst .copyLengthSecond .encodeLength
    (.build .candidate .bitFirst) A (trailingLengthEncodingRegs k) (trailingLengthEncodingRegs_injective k)
    (by rfl) (by rfl) (by rfl) C4 rfl rfl x.length (by simp [C4, C3, trailingLengthEncodingRegs])
    (by simp [C4, C3, trailingLengthEncodingRegs, hc.first])
    (by simp [C4, C3, trailingLengthEncodingRegs, hc.second])
    (by simp [C4, C3, trailingLengthEncodingRegs, hc.tmp])
    (by simp [C4, C3, trailingLengthEncodingRegs, hc.scratch])
  have hreg : trailingLengthEncodingRegs k 3 = trailingRegIndex .inputPrefix := rfl
  rw [hreg] at h5
  have h12 : (trailingBaseProgram k).exec A cfg ((7 * x.length + 3) + lengthCountTime 0 x.length) = C2 := by
    rw [StackProgram.exec_add, h1, h2]
  have h123 : (trailingBaseProgram k).exec A cfg
      ((7 * x.length + 3) + lengthCountTime 0 x.length + (2 * x.length.bits.length + 1)) = C3 := by
    rw [StackProgram.exec_add, h12, h3]
  have h1234 : (trailingBaseProgram k).exec A cfg
      ((7 * x.length + 3) + lengthCountTime 0 x.length + (2 * x.length.bits.length + 1) + (7 * x.length + 3)) = C4 := by
    rw [StackProgram.exec_add, h123, h4]
  rw [StackProgram.exec_add, h1234]
  unfold trailingBaseProgram
  rw [h5]
  simp only [C4, C3, Function.update_self, Function.update_idem]

end APSCounting893.Main
end Component_28

section Component_29
set_option autoImplicit false
namespace APSCounting893.Main
lemma bits_length_le_of_lt_pow (a p : ℕ) (h : a < 2 ^ p) : a.bits.length ≤ p := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr h

lemma bits_length_le_self (a : ℕ) : a.bits.length ≤ a :=
  bits_length_le_of_lt_pow a a a.lt_two_pow_self

lemma bits_length_le_of_le_pow (a p : ℕ) (h : a ≤ 2 ^ p) : a.bits.length ≤ p + 1 := by
  apply bits_length_le_of_lt_pow
  have hp : 0 < 2 ^ p := by positivity
  rw [pow_succ]
  omega


end APSCounting893.Main
end Component_29

section Component_30

set_option autoImplicit false
namespace APSCounting893.Main

lemma trailing_input_prefix_time_bound (n : ℕ) :
    (7 * n + 3) + lengthCountTime 0 n + (2 * n.bits.length + 1) +
      (7 * n + 3) + (18 * n.bits.length + 9) ≤ 100 * (n + 1) ^ 2 := by
  have h := lengthCountTime_bound 0 n
  have hb := bits_length_le_self n
  nlinarith

lemma trailing_build_query_time_bound (k N xLength bitLength B : ℕ)
    (hx : xLength ≤ N) (hb : bitLength ≤ N) (hB : B ≤ N) :
    18 * bitLength + 9 + 4 + (1 + (k + 1) * (18 * B + 9)) +
      (encodeNat (k + 1)).length + 2 + 7 * (encodeNat xLength).length + 7 * xLength + 3 ≤
      100 * (k + 2) * (N + 1) := by
  have hk := bits_length_le_self (k + 1)
  have hl := bits_length_le_self xLength
  simp only [encodeNat, List.length_append, List.length_replicate, List.length_singleton]
  nlinarith [Nat.mul_le_mul_left (k + 1) hB, Nat.zero_le (k * N)]

end APSCounting893.Main
end Component_30

section Component_31
set_option autoImplicit false
namespace APSCounting893.Main
lemma orderExponent_apply_not_mem {n : ℕ} (order : List (Fin n)) (a : Fin n →₀ ℕ)
    (v : Fin n) (hv : v ∉ order) : orderExponent order a v = 0 := by
  classical
  induction order with
  | nil => simp [orderExponent]
  | cons w order ih =>
      have hvw : v ≠ w := by intro h; subst v; exact hv (by simp)
      have hv' : v ∉ order := by intro h; exact hv (List.mem_cons_of_mem w h)
      simp [orderExponent, Finsupp.single_apply, hvw, hvw.symm,
        show ((order.map (fun w => Finsupp.single w (a w))).sum) v = 0 from ih hv']


end APSCounting893.Main
end Component_31

section Component_32

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main

lemma orderExponent_apply_mem {n : ℕ} (order : List (Fin n)) (a : Fin n →₀ ℕ)
    (hd : order.Nodup) (v : Fin n) (hv : v ∈ order) : orderExponent order a v = a v := by
  classical
  induction order with
  | nil => simp at hv
  | cons w ws ih =>
      rcases List.nodup_cons.mp hd with ⟨hw, hws⟩
      rcases List.mem_cons.mp hv with h | h
      · subst v
        have hz := orderExponent_apply_not_mem ws a w hw
        simpa [orderExponent, Finsupp.add_apply, Finsupp.single_apply] using hz
      · have hne : v ≠ w := by intro he; subst v; exact hw h
        have hh := ih hws h
        simpa [orderExponent, Finsupp.add_apply, Finsupp.single_apply, hne, hne.symm] using hh

lemma firstCoordinates_mem_iff {k : ℕ} (v : Fin (k + 1)) :
    v ∈ List.ofFn (fun i : Fin k => i.castSucc) ↔ v ≠ Fin.last k := by
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact Fin.castSucc_ne_last i
  · intro h
    have hv : v.val < k := by
      have hle : v.val ≤ k := Nat.le_of_lt_succ v.isLt
      have hne : v.val ≠ k := by intro he; apply h; exact Fin.ext he
      omega
    exact ⟨⟨v.val, hv⟩, Fin.ext rfl⟩

lemma orderExponent_firstCoordinates {k : ℕ} (a : Fin (k + 1) →₀ ℕ) (v : Fin (k + 1)) :
    orderExponent (List.ofFn (fun i : Fin k => i.castSucc)) a v =
      if v = Fin.last k then 0 else a v := by
  classical
  by_cases hv : v = Fin.last k
  · rw [if_pos hv]
    exact orderExponent_apply_not_mem _ _ _ (by simpa only [firstCoordinates_mem_iff] using not_not_intro hv)
  · rw [if_neg hv]
    apply orderExponent_apply_mem _ _ _ _ ((firstCoordinates_mem_iff v).mpr hv)
    exact List.nodup_ofFn.mpr (Fin.castSucc_injective k)

end APSCounting893.Main
end Component_32

section Component_33

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma trailing_build_two_queries {k : ℕ} (A : Language) (cfg : TrailingConfig k)
    (hs : cfg.state = .at (.build .earlier .bitFirst) .entry) (ha : cfg.answer = none) (hc : TrailingClean cfg)
    (x : Word) (e a : Fin (k + 1) →₀ ℕ) (qE qF N : ℕ)
    (hx : x.length ≤ N) (hqe : qE.bits.length ≤ N) (hqf : qF.bits.length ≤ N)
    (hbitsE : cfg.regs (trailingRegIndex .qE) = qE.bits.reverse)
    (hbitsF : cfg.regs (trailingRegIndex .qF) = qF.bits.reverse)
    (hfieldsE : ∀ i, cfg.regs (trailingRegIndex (.eField i)) = (e i).bits.reverse)
    (hfieldsA : ∀ i, cfg.regs (trailingRegIndex (.aField i)) = (a i).bits.reverse)
    (hBE : ∀ i, (e i).bits.length ≤ N) (hBA : ∀ i, (a i).bits.length ≤ N)
    (hp : cfg.regs (trailingRegIndex .inputPrefix) = encodeNat x.length ++ x)
    (hEempty : cfg.regs (trailingRegIndex .queryE) = []) (hFempty : cfg.regs (trailingRegIndex .queryF) = []) :
    ∃ t ≤ 200 * (k + 2) * (N + 1), (trailingBaseProgram k).exec A cfg t =
      { state := .at (.compareBegin 0) .entry,
        regs := Function.update (Function.update cfg.regs (trailingRegIndex .queryE)
          (coefficientQuery x e .numerator qE)) (trailingRegIndex .queryF)
          (coefficientQuery x (orderExponent (List.ofFn (fun i : Fin k => i.castSucc)) a) .numerator qF),
        answer := none } := by
  classical
  let af := orderExponent (List.ofFn (fun i : Fin k => i.castSucc)) a
  obtain ⟨t, ht, hex⟩ := trailing_build_query A .earlier cfg hs ha hc x e qE N hbitsE
    (by intro i; exact Or.inr (hfieldsE i)) (by intro h; cases h) hBE hp hEempty
  let C : TrailingConfig k :=
    { state := .at (.build .final .bitFirst) .entry,
      regs := Function.update cfg.regs (trailingRegIndex .queryE) (coefficientQuery x e .numerator qE), answer := none }
  have hex' : (trailingBaseProgram k).exec A cfg t = C := hex
  have hcC : TrailingClean C := trailing_clean_query_update cfg hc .earlier _ _ _
  have hbitsFC : C.regs (trailingBitReg .final) = qF.bits.reverse := by
    simpa [C, trailingBitReg] using hbitsF
  have hfieldsFC : ∀ i : Fin (k + 1), (TrailingQuery.final = .final ∧ i = Fin.last k) ∨
      C.regs (trailingFieldReg .final i) = (af i).bits.reverse := by
    intro i
    by_cases hi : i = Fin.last k
    · exact Or.inl ⟨rfl, hi⟩
    · right
      simpa only [C, trailingFieldReg, Function.update_of_ne
        (by simp : trailingRegIndex (TrailingReg.aField i) ≠ trailingRegIndex .queryE),
        af, orderExponent_firstCoordinates, if_neg hi] using hfieldsA i
  have hz : TrailingQuery.final = .final → af (Fin.last k) = 0 := by
    intro h; simp [af, orderExponent_firstCoordinates]
  have hBF : ∀ i, (af i).bits.length ≤ N := by
    intro i
    by_cases hi : i = Fin.last k
    · simp [af, orderExponent_firstCoordinates, hi]
    · simpa only [af, orderExponent_firstCoordinates, if_neg hi] using hBA i
  have hpC : C.regs (trailingRegIndex .inputPrefix) = encodeNat x.length ++ x := by simpa [C] using hp
  have hFC : C.regs (trailingQueryReg .final) = [] := by simpa [C, trailingQueryReg] using hFempty
  obtain ⟨s, hsB, heF⟩ := trailing_build_query A .final C rfl rfl hcC x af qF N
    hbitsFC hfieldsFC hz hBF hpC hFC
  have htimeE : t ≤ 100 * (k + 2) * (N + 1) := by
    apply ht.trans
    have hh := trailing_build_query_time_bound k N x.length qE.bits.length N hx hqe le_rfl
    simpa only [List.length_append, Nat.mul_add, Nat.add_assoc] using hh
  have htimeF : s ≤ 100 * (k + 2) * (N + 1) := by
    apply hsB.trans
    have hh := trailing_build_query_time_bound k N x.length qF.bits.length N hx hqf le_rfl
    simpa only [List.length_append, Nat.mul_add, Nat.add_assoc] using hh
  refine ⟨t + s, by nlinarith, ?_⟩
  rw [StackProgram.exec_add, hex', heF]
  rfl

end APSCounting893.Main
end Component_33

section Component_34

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma assemble_compareLength {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r)
    (initial q less equal greater : Q) (A : Language) (left right : Fin (r + 2)) (hne : left ≠ right)
    (ht : table q = .compareLength left right less equal greater)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none)
    (x y : Word) (hx : cfg.regs left = x) (hy : cfg.regs right = y) :
    (assemble table initial).exec A cfg (2 * min x.length y.length + 2) =
      { state := if x.length < y.length then .at less .entry else
          if y.length < x.length then .at greater .entry else .at equal .entry,
        regs := Function.update (Function.update cfg.regs left (x.drop (min x.length y.length + 1))) right
          (y.drop (min x.length y.length + 1)), answer := none } := by
  exact stack_length_compare_routine (assemble table initial) A left right hne
    (.at q .entry) (.at q .p1) (.at q .p2) (.at less .entry) (.at equal .entry) (.at greater .entry)
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht]) cfg hs ha x y hx hy

lemma assemble_compareLex {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r)
    (initial q less equal greater : Q) (A : Language) (left right : Fin (r + 2)) (hne : left ≠ right)
    (ht : table q = .compareLex left right less equal greater)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none)
    (x y : Word) (hx : cfg.regs left = x) (hy : cfg.regs right = y) :
    ∃ t ≤ 2 * (min x.length y.length + 1),
      ((assemble table initial).exec A cfg t).state =
        comparisonState (.at less .entry) (.at equal .entry) (.at greater .entry) (wordCompare x y) ∧
      ((assemble table initial).exec A cfg t).answer = none ∧
      ∀ j, j ≠ left → j ≠ right → ((assemble table initial).exec A cfg t).regs j = cfg.regs j := by
  exact stack_word_compare_routine (assemble table initial) A left right hne
    (.at q .entry) (.at q .p1) (.at q .p2) (.at q .p3) (.at less .entry) (.at equal .entry) (.at greater .entry)
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht])
    cfg hs ha x y hx hy

lemma assemble_query {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r)
    (initial q yes no : Q) (A : Language) (reg : Fin (r + 2))
    (ht : table q = .query reg yes no)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none) :
    (assemble table initial).step A cfg =
      { state := (@ite _ (A (cfg.regs reg)) (Classical.propDecidable _) (.at yes .entry) (.at no .entry)),
        regs := Function.update cfg.regs reg [], answer := none } := by
  classical
  simp [StackProgram.step, hs, ha, assemble, ht]

lemma assemble_jump {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r)
    (initial q next : Q) (A : Language) (ht : table q = .jump next)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none) :
    (assemble table initial).step A cfg = { cfg with state := .at next .entry } := by
  simp [StackProgram.step, hs, ha, assemble, ht]

lemma assemble_push {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r)
    (initial q next : Q) (A : Language) (dst : Fin (r + 2)) (b : Bool) (ht : table q = .push dst b next)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none) :
    (assemble table initial).step A cfg =
      { state := .at next .entry, regs := Function.update cfg.regs dst (b :: cfg.regs dst), answer := none } := by
  simp [StackProgram.step, hs, ha, assemble, ht]

lemma assemble_halt {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r)
    (initial q : Q) (A : Language) (b : Bool) (ht : table q = .halt b)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none) :
    (assemble table initial).step A cfg = { cfg with answer := some b } := by
  simp [StackProgram.step, hs, ha, assemble, ht]

lemma assemble_failure_halt {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r)
    (initial : Q) (A : Language) (b : Bool)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .halt b) (ha : cfg.answer = none) :
    (assemble table initial).step A cfg = { cfg with answer := some b } := by
  simp [StackProgram.step, hs, ha, assemble]

end APSCounting893.Main
end Component_34

section Component_35
set_option autoImplicit false
namespace APSCounting893.Main

end APSCounting893.Main
end Component_35

section Component_36

set_option autoImplicit false
namespace APSCounting893.Main

lemma comparisonState_bits_of_length_eq {Q : Type} (less equal greater : Q) (n m : ℕ)
    (hlen : n.bits.length = m.bits.length) :
    comparisonState less equal greater (wordCompare n.bits.reverse m.bits.reverse) =
      if n < m then less else if m < n then greater else equal := by
  rcases lt_trichotomy n m with h | h | h
  · have hw : wordCompare n.bits.reverse m.bits.reverse = .lt := by
      apply (wordCompare_lt_iff _ _).mpr
      exact (((nat_lt_iff_bits_length_lex n m).mp h).resolve_left (by omega)).2
    simp [hw, comparisonState, h]
  · subst m
    simp [comparisonState, (wordCompare_eq_iff _ _).mpr (rfl : n.bits.reverse = n.bits.reverse)]
  · have hw : wordCompare n.bits.reverse m.bits.reverse = .gt := by
      apply (wordCompare_gt_iff _ _).mpr
      exact (((nat_lt_iff_bits_length_lex m n).mp h).resolve_left (by omega)).2
    simp [hw, comparisonState, h, Nat.not_lt_of_gt h]

end APSCounting893.Main
end Component_36

section Component_37

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma trailing_compare_lengths {k : ℕ} (A : Language) (i : Fin (k + 1)) (hi : i.val < k)
    (cfg : TrailingConfig k) (hs : cfg.state = .at (.compareBegin i) .entry) (ha : cfg.answer = none)
    (n m : ℕ) (he : cfg.regs (trailingRegIndex (.eField i)) = n.bits.reverse)
    (heA : cfg.regs (trailingRegIndex (.aField i)) = m.bits.reverse)
    (htmp : cfg.regs (trailingRegIndex .copyTmp) = [])
    (hscratch : cfg.regs (trailingRegIndex .copyScratch) = [])
    (hl : cfg.regs (trailingRegIndex .leftClone) = [])
    (hr : cfg.regs (trailingRegIndex .rightClone) = []) :
    (trailingBaseProgram k).exec A cfg
      ((7 * n.bits.length + 3) + (7 * m.bits.length + 3) + (2 * min n.bits.length m.bits.length + 2)) =
      { state := if n.bits.length < m.bits.length then .at .askE .entry else
          if m.bits.length < n.bits.length then .at .askF .entry else .at (.compareBits i) .entry,
        regs := Function.update (Function.update cfg.regs (trailingRegIndex .leftClone)
          (n.bits.reverse.drop (min n.bits.length m.bits.length + 1))) (trailingRegIndex .rightClone)
          (m.bits.reverse.drop (min n.bits.length m.bits.length + 1)), answer := none } := by
  classical
  let C1 : TrailingConfig k :=
    { state := .at (.compareRight i) .entry,
      regs := Function.update cfg.regs (trailingRegIndex .leftClone) n.bits.reverse, answer := none }
  have h1 : (trailingBaseProgram k).exec A cfg (7 * n.bits.length + 3) = C1 := by
    have hh := assemble_copy_clean (trailingTable k) .outerPair (.compareBegin i) (.compareRight i) A
      (trailingRegIndex (.eField i)) (trailingRegIndex .leftClone)
      (trailingRegIndex .copyTmp) (trailingRegIndex .copyScratch)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp [trailingTable, hi]) cfg hs ha n.bits.reverse he htmp hscratch
    simpa only [trailingBaseProgram, List.length_reverse, hl, List.append_nil] using hh
  let C2 : TrailingConfig k :=
    { state := .at (.compareLengths i) .entry,
      regs := Function.update C1.regs (trailingRegIndex .rightClone) m.bits.reverse, answer := none }
  have h2 : (trailingBaseProgram k).exec A C1 (7 * m.bits.length + 3) = C2 := by
    have hh := assemble_copy_clean (trailingTable k) .outerPair (.compareRight i) (.compareLengths i) A
      (trailingRegIndex (.aField i)) (trailingRegIndex .rightClone)
      (trailingRegIndex .copyTmp) (trailingRegIndex .copyScratch)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by rfl) C1 rfl rfl m.bits.reverse (by simpa [C1] using heA)
      (by simpa [C1] using htmp) (by simpa [C1] using hscratch)
    simpa only [trailingBaseProgram, List.length_reverse, C1, Function.update_of_ne
      (by simp : trailingRegIndex (k := k) .rightClone ≠ trailingRegIndex .leftClone), hr, List.append_nil] using hh
  have h3 := assemble_compareLength (trailingTable k) .outerPair (.compareLengths i) .askE (.compareBits i) .askF A
    (trailingRegIndex .leftClone) (trailingRegIndex .rightClone) (by simp) (by rfl)
    C2 rfl rfl n.bits.reverse m.bits.reverse (by simp [C2, C1]) (by simp [C2])
  have h12 : (trailingBaseProgram k).exec A cfg ((7 * n.bits.length + 3) + (7 * m.bits.length + 3)) = C2 := by
    rw [StackProgram.exec_add, h1, h2]
  rw [StackProgram.exec_add, h12]
  unfold trailingBaseProgram
  simpa only [List.length_reverse, C2, C1, Function.update_idem,
    Function.update_comm (by simp : trailingRegIndex (k := k) .leftClone ≠ trailingRegIndex .rightClone)] using h3

end APSCounting893.Main
end Component_37

section Component_38

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma trailing_compare_coordinate {k : ℕ} (A : Language) (i : Fin (k + 1)) (hi : i.val < k)
    (cfg : TrailingConfig k) (hs : cfg.state = .at (.compareBegin i) .entry) (ha : cfg.answer = none)
    (n m : ℕ) (he : cfg.regs (trailingRegIndex (.eField i)) = n.bits.reverse)
    (heA : cfg.regs (trailingRegIndex (.aField i)) = m.bits.reverse)
    (htmp : cfg.regs (trailingRegIndex .copyTmp) = [])
    (hscratch : cfg.regs (trailingRegIndex .copyScratch) = [])
    (hl : cfg.regs (trailingRegIndex .leftClone) = [])
    (hr : cfg.regs (trailingRegIndex .rightClone) = []) :
    ∃ t ≤ 20 * (n.bits.length + m.bits.length + 1), ∃ out,
      (trailingBaseProgram k).exec A cfg t = out ∧
      out.state = .at (if n < m then .askE else if m < n then .askF else trailingNextCompare i) .entry ∧
      out.answer = none ∧
      (n = m → out.regs (trailingRegIndex .leftClone) = [] ∧ out.regs (trailingRegIndex .rightClone) = []) ∧
      (∀ j, j ≠ trailingRegIndex .leftClone → j ≠ trailingRegIndex .rightClone →
        j ≠ trailingRegIndex (.eField i) → j ≠ trailingRegIndex (.aField i) → out.regs j = cfg.regs j) := by
  classical
  let cost := (7 * n.bits.length + 3) + (7 * m.bits.length + 3) + (2 * min n.bits.length m.bits.length + 2)
  let C : TrailingConfig k :=
    { state := if n.bits.length < m.bits.length then .at .askE .entry else
          if m.bits.length < n.bits.length then .at .askF .entry else .at (.compareBits i) .entry,
      regs := Function.update (Function.update cfg.regs (trailingRegIndex .leftClone)
        (n.bits.reverse.drop (min n.bits.length m.bits.length + 1))) (trailingRegIndex .rightClone)
        (m.bits.reverse.drop (min n.bits.length m.bits.length + 1)), answer := none }
  have hex : (trailingBaseProgram k).exec A cfg cost = C :=
    trailing_compare_lengths A i hi cfg hs ha n m he heA htmp hscratch hl hr
  have hcost : cost + 2 * (min n.bits.length m.bits.length + 1) ≤
      20 * (n.bits.length + m.bits.length + 1) := by
    have hmn := Nat.min_le_left n.bits.length m.bits.length
    have hnm := Nat.min_le_right n.bits.length m.bits.length
    dsimp only [cost]
    omega
  have hframe : ∀ j, j ≠ trailingRegIndex .leftClone → j ≠ trailingRegIndex .rightClone → C.regs j = cfg.regs j := by
    intro j hjl hjr
    simp only [C, Function.update_of_ne hjr, Function.update_of_ne hjl]
  by_cases hlt : n.bits.length < m.bits.length
  · have hnm := nat_bits_length_lt_implies_lt n m hlt
    refine ⟨cost, by omega, C, hex, ?_, rfl, ?_, ?_⟩
    · simp [C, hlt, hnm]
    · intro heq; subst m; omega
    · intro j hjl hjr hje hja; exact hframe j hjl hjr
  · by_cases hgt : m.bits.length < n.bits.length
    · have hmn := nat_bits_length_lt_implies_lt m n hgt
      refine ⟨cost, by omega, C, hex, ?_, rfl, ?_, ?_⟩
      · simp [C, hlt, hgt, hmn, Nat.not_lt_of_gt hmn]
      · intro heq; subst m; omega
      · intro j hjl hjr hje hja; exact hframe j hjl hjr
    · have hlen : n.bits.length = m.bits.length := by omega
      have hsC : C.state = .at (.compareBits i) .entry := by simp [C, hlt, hgt]
      have hE : C.regs (trailingRegIndex (.eField i)) = n.bits.reverse := by
        rw [hframe (trailingRegIndex (.eField i)) (by simp) (by simp), he]
      have hA : C.regs (trailingRegIndex (.aField i)) = m.bits.reverse := by
        rw [hframe (trailingRegIndex (.aField i)) (by simp) (by simp), heA]
      obtain ⟨t, ht, hst, hans, hfr⟩ := assemble_compareLex (trailingTable k) .outerPair
        (.compareBits i) .askE (trailingNextCompare i) .askF A
        (trailingRegIndex (.eField i)) (trailingRegIndex (.aField i)) (by simp)
        (by rfl) C hsC rfl n.bits.reverse m.bits.reverse hE hA
      let out := (trailingBaseProgram k).exec A C t
      have hst' : out.state = .at (if n < m then .askE else if m < n then .askF else trailingNextCompare i) .entry := by
        have hh := comparisonState_bits_of_length_eq
          (Q := AssemblyControl (TrailingSite k) (assemblyConstantBound (trailingTable k)))
          (AssemblyControl.at (TrailingSite.askE : TrailingSite k) AssemblyPhase.entry)
          (.at (trailingNextCompare i) .entry) (.at .askF .entry) n m hlen
        rw [hh] at hst
        by_cases hnm : n < m
        · simpa only [out, trailingBaseProgram, if_pos hnm] using hst
        · by_cases hmn : m < n
          · simpa only [out, trailingBaseProgram, if_neg hnm, if_pos hmn] using hst
          · simpa only [out, trailingBaseProgram, if_neg hnm, if_neg hmn] using hst
      refine ⟨cost + t, ?_, out, ?_, hst', hans, ?_, ?_⟩
      · simp only [List.length_reverse] at ht
        omega
      · rw [StackProgram.exec_add, hex]
      · intro heq
        have hlC : C.regs (trailingRegIndex .leftClone) = [] := by
          simp [C, hlen]
        have hrC : C.regs (trailingRegIndex .rightClone) = [] := by
          simp [C, hlen]
        constructor
        · simp only [out, trailingBaseProgram]
          rw [hfr (trailingRegIndex .leftClone) (by simp) (by simp), hlC]
        · simp only [out, trailingBaseProgram]
          rw [hfr (trailingRegIndex .rightClone) (by simp) (by simp), hrC]
      · intro j hjl hjr hje hja
        simp only [out, trailingBaseProgram]
        rw [hfr j hje hja, hframe j hjl hjr]

end APSCounting893.Main
end Component_38

section Component_39

set_option autoImplicit false
namespace APSCounting893.Main

def trailingSuffix {k : ℕ} (a : Fin (k + 1) →₀ ℕ) (n : ℕ) : List ℕ :=
  (List.ofFn (fun i : Fin k => a i.castSucc)).drop n

lemma trailingSuffix_end {k : ℕ} (a : Fin (k + 1) →₀ ℕ) : trailingSuffix a k = [] := by
  simp [trailingSuffix]

lemma trailingSuffix_cons {k : ℕ} (a : Fin (k + 1) →₀ ℕ) (n : ℕ) (hn : n < k) :
    trailingSuffix a n = a ⟨n, by omega⟩ :: trailingSuffix a (n + 1) := by
  unfold trailingSuffix
  rw [List.drop_eq_getElem_cons (by simpa using hn)]
  simp only [List.getElem_ofFn]
  have hidx : (⟨n, hn⟩ : Fin k).castSucc = (⟨n, by omega⟩ : Fin (k + 1)) := Fin.ext rfl
  exact congrArg (fun i => a i :: (List.ofFn (fun i : Fin k => a i.castSucc)).drop (n + 1)) hidx

lemma trailingSuffix_lex_step {k : ℕ} (e a : Fin (k + 1) →₀ ℕ) (n : ℕ) (hn : n < k) :
    List.Lex (· < ·) (trailingSuffix e n) (trailingSuffix a n) ↔
      e ⟨n, by omega⟩ < a ⟨n, by omega⟩ ∨
        (e ⟨n, by omega⟩ = a ⟨n, by omega⟩ ∧
          List.Lex (· < ·) (trailingSuffix e (n + 1)) (trailingSuffix a (n + 1))) := by
  rw [trailingSuffix_cons e n hn, trailingSuffix_cons a n hn, List.cons_lex_cons_iff]

end APSCounting893.Main
end Component_39

section Component_40

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def TrailingCompareSafe {k : ℕ} (j : Fin (Fintype.card (TrailingReg k) + 2)) : Prop :=
  j ≠ trailingRegIndex .leftClone ∧ j ≠ trailingRegIndex .rightClone ∧
    ∀ i : Fin (k + 1), j ≠ trailingRegIndex (.eField i) ∧ j ≠ trailingRegIndex (.aField i)

lemma trailing_compare_loop {k : ℕ} (A : Language) (e a : Fin (k + 1) →₀ ℕ)
    (B remaining n : ℕ) (hn : n + remaining = k)
    (hB : ∀ i, (e i).bits.length ≤ B ∧ (a i).bits.length ≤ B)
    (cfg : TrailingConfig k) (hs : cfg.state = .at (.compareBegin ⟨n, by omega⟩) .entry)
    (ha : cfg.answer = none)
    (hv : ∀ i : Fin (k + 1), n ≤ i.val →
      cfg.regs (trailingRegIndex (.eField i)) = (e i).bits.reverse ∧
      cfg.regs (trailingRegIndex (.aField i)) = (a i).bits.reverse)
    (htmp : cfg.regs (trailingRegIndex .copyTmp) = [])
    (hscratch : cfg.regs (trailingRegIndex .copyScratch) = [])
    (hl : cfg.regs (trailingRegIndex .leftClone) = [])
    (hr : cfg.regs (trailingRegIndex .rightClone) = []) :
    ∃ t ≤ 1 + remaining * (20 * (2 * B + 1)), ∃ out,
      (trailingBaseProgram k).exec A cfg t = out ∧
      out.state = .at (if List.Lex (· < ·) (trailingSuffix e n) (trailingSuffix a n) then .askE else .askF) .entry ∧
      out.answer = none ∧ (∀ j, TrailingCompareSafe j → out.regs j = cfg.regs j) := by
  classical
  induction remaining generalizing n cfg with
  | zero =>
      have hnk : n = k := by omega
      subst n
      let out : TrailingConfig k := { cfg with state := .at .askF .entry }
      have he : (trailingBaseProgram k).exec A cfg 1 = out := by
        have hh := assemble_jump (trailingTable k) .outerPair (.compareBegin ⟨k, by omega⟩) .askF A
          (by simp [trailingTable]) cfg hs ha
        exact hh
      refine ⟨1, by simp, out, he, ?_, ha, ?_⟩
      · simp [out, trailingSuffix_end]
      · intro j hj; rfl
  | succ remaining ih =>
      have hnk : n < k := by omega
      let i0 : Fin (k + 1) := ⟨n, by omega⟩
      obtain ⟨t, ht, C, hex, hst, hans, hclones, hframe⟩ :=
        trailing_compare_coordinate A i0 hnk cfg hs ha (e i0) (a i0)
          (hv i0 le_rfl).1 (hv i0 le_rfl).2 htmp hscratch hl hr
      have hcost : t ≤ 20 * (2 * B + 1) := by
        have hb := hB i0
        omega
      have hframeSafe (j) (hj : TrailingCompareSafe (k := k) j) : C.regs j = cfg.regs j :=
        hframe j hj.1 hj.2.1 (hj.2.2 i0).1 (hj.2.2 i0).2
      by_cases hlt : e i0 < a i0
      · have hlex : List.Lex (· < ·) (trailingSuffix e n) (trailingSuffix a n) :=
          (trailingSuffix_lex_step e a n hnk).mpr (Or.inl hlt)
        refine ⟨t, by nlinarith, C, hex, ?_, hans, hframeSafe⟩
        simp only [if_pos hlt] at hst
        simpa only [if_pos hlex] using hst
      · by_cases hgt : a i0 < e i0
        · have hlex : ¬ List.Lex (· < ·) (trailingSuffix e n) (trailingSuffix a n) := by
            rw [trailingSuffix_lex_step e a n hnk]
            rintro (he | ⟨he, _⟩)
            · change e i0 < a i0 at he
              omega
            · change e i0 = a i0 at he
              omega
          refine ⟨t, by nlinarith, C, hex, ?_, hans, hframeSafe⟩
          simp only [if_neg hlt, if_pos hgt] at hst
          simpa only [if_neg hlex] using hst
        · have heq : e i0 = a i0 := by omega
          have hsC : C.state = .at (.compareBegin ⟨n + 1, by omega⟩) .entry := by
            simpa only [if_neg hlt, if_neg hgt, trailingNextCompare,
              dif_pos (show i0.val + 1 < k + 1 by dsimp [i0]; omega)] using hst
          have hvC : ∀ i : Fin (k + 1), n + 1 ≤ i.val →
              C.regs (trailingRegIndex (.eField i)) = (e i).bits.reverse ∧
              C.regs (trailingRegIndex (.aField i)) = (a i).bits.reverse := by
            intro i hi
            have hne : i ≠ i0 := by intro he; have hh := congrArg Fin.val he; change i.val = n at hh; omega
            constructor
            · rw [hframe (trailingRegIndex (.eField i)) (by simp) (by simp) (by simpa using hne) (by simp)]
              exact (hv i (by omega)).1
            · rw [hframe (trailingRegIndex (.aField i)) (by simp) (by simp) (by simp) (by simpa using hne)]
              exact (hv i (by omega)).2
          have htC : C.regs (trailingRegIndex .copyTmp) = [] := by
            rw [hframe (trailingRegIndex .copyTmp) (by simp) (by simp) (by simp) (by simp), htmp]
          have hsC' : C.regs (trailingRegIndex .copyScratch) = [] := by
            rw [hframe (trailingRegIndex .copyScratch) (by simp) (by simp) (by simp) (by simp), hscratch]
          obtain ⟨s, hsB, out, he, hst2, hans2, hframe2⟩ := ih (n + 1) (by omega) C hsC hans hvC htC hsC'
            (hclones heq).1 (hclones heq).2
          have hlexeq : List.Lex (· < ·) (trailingSuffix e n) (trailingSuffix a n) ↔
              List.Lex (· < ·) (trailingSuffix e (n + 1)) (trailingSuffix a (n + 1)) := by
            rw [trailingSuffix_lex_step e a n hnk]
            change e i0 < a i0 ∨ (e i0 = a i0 ∧ _) ↔ _
            simp only [heq, lt_self_iff_false, false_or, true_and]
          refine ⟨t + s, by nlinarith, out, ?_, ?_, hans2, ?_⟩
          · rw [StackProgram.exec_add, hex, he]
          · simpa only [← hlexeq] using hst2
          · intro j hj
            rw [hframe2 j hj, hframeSafe j hj]

end APSCounting893.Main
end Component_40

section Component_41

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main

lemma stack_nat_parser_failure {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src counter dst : Fin (r + 2)) (hsc : src ≠ counter) (hsd : src ≠ dst) (hcd : counter ≠ dst)
    (unary save bitsLoop value zero one check finish fail : Q)
    (hunary : P.transition unary = .pop src bitsLoop save fail)
    (hsave : P.transition save = .push counter true unary)
    (hbits : P.transition bitsLoop = .pop counter value value check)
    (hvalue : P.transition value = .pop src zero one fail)
    (hzero : P.transition zero = .push dst false bitsLoop)
    (hone : P.transition one = .push dst true bitsLoop)
    (hcheck : P.transition check = .peek dst fail finish finish)
    (cfg : StackConfig Q r) (hs : cfg.state = unary) (ha : cfg.answer = none)
    (v : Word) (hw : cfg.regs src = v) (hc : cfg.regs counter = []) (hd : cfg.regs dst = []) (hbad : decodeNat v = none) :
    ∃ t ≤ 5 * v.length + 3, (P.exec A cfg t).answer = none ∧
      (P.exec A cfg t).state = fail := by
  classical
  cases hu : readUnary v with
  | none =>
      have hraw := (readUnary_none_iff v).mp hu
      have ht := stack_unary_missing_routine P A src counter hsc unary save bitsLoop fail
        hunary hsave cfg hs ha v.length (hw.trans hraw)
      refine ⟨2 * v.length + 1, by omega, ?_⟩
      rw [ht]
      exact ⟨rfl, rfl⟩
  | some p =>
      rcases p with ⟨k, rest⟩
      have hraw := readUnary_inverse v k rest hu
      have hvlen := readUnary_length v k rest hu
      have hinput := hw.trans hraw
      by_cases hlen : k ≤ rest.length
      · have hbitslen : (rest.take k).length = k := by simp [List.length_take, Nat.min_eq_left hlen]
        have hinput' : cfg.regs src = List.replicate (rest.take k).length true ++
            false :: ((rest.take k) ++ rest.drop k) := by
          rw [hbitslen, List.take_append_drop]
          exact hinput
        have ht := stack_binary_field_routine P A src counter dst hsc hsd hcd unary save bitsLoop value zero one check finish fail
          hunary hsave hbits hvalue hzero hone hcheck cfg hs ha (rest.take k) (rest.drop k) hinput' hc hd
        refine ⟨5 * (rest.take k).length + 3, by omega, ?_⟩
        rw [ht]
        refine ⟨rfl, ?_⟩
        have hcan : canonicalBits (rest.take k) ≠ true := by
          intro hcan
          simp [decodeNat, hu, hlen, hcan] at hbad
        simp [hcan]
      · let cfg1 : StackConfig Q r :=
          { state := bitsLoop,
            regs := Function.update (Function.update cfg.regs src rest) counter (List.replicate k true), answer := none }
        have ht1 : P.exec A cfg (2 * k + 1) = cfg1 := by
          have ht := stack_unary_routine P A src counter hsc unary save bitsLoop fail hunary hsave cfg hs ha k rest hinput
          simpa only [hc, List.append_nil] using ht
        have hw1 : cfg1.regs src = rest := by simp [cfg1, hsc]
        have hc1 : cfg1.regs counter = List.replicate k true := by simp [cfg1]
        have ht2 := stack_truncated_bits_routine P A src counter dst hsc hsd hcd bitsLoop value zero one check fail
          hbits hvalue hzero hone cfg1 rfl rfl rest hw1 k hc1 (by omega)
        refine ⟨(2 * k + 1) + (3 * rest.length + 2), by omega, ?_⟩
        rw [StackProgram.exec_add, ht1]
        exact ⟨ht2.2, ht2.1⟩


end APSCounting893.Main
end Component_41

section Component_42

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma assemble_nat_failure {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r) (initial q next : Q)
    (A : Language) (src counter dst : Fin (r + 2)) (hsc : src ≠ counter) (hsd : src ≠ dst) (hcd : counter ≠ dst)
    (failure : Bool) (ht : table q = .nat src counter dst next failure)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) (hc : cfg.regs counter = []) (hd : cfg.regs dst = [])
    (hbad : decodeNat w = none) :
    ∃ t ≤ 5 * w.length + 3, ((assemble table initial).exec A cfg t).answer = none ∧
      ((assemble table initial).exec A cfg t).state = .halt failure := by
  exact stack_nat_parser_failure (assemble table initial) A src counter dst hsc hsd hcd
    (.at q .entry) (.at q .p1) (.at q .p2) (.at q .p3) (.at q .p4) (.at q .p5) (.at q .p6)
    (.at next .entry) (.halt failure)
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht])
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht])
    cfg hs ha w hw hc hd hbad

lemma assemble_pair_failure {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r) (initial q next : Q)
    (A : Language) (src dst : Fin (r + 2)) (hne : src ≠ dst) (failure : Bool)
    (ht : table q = .pair src dst next failure)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at q .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) (hbad : decodePair w = none) :
    ∃ t ≤ 3 * w.length + 2, ((assemble table initial).exec A cfg t).answer = none ∧
      ((assemble table initial).exec A cfg t).state = .halt failure := by
  obtain ⟨t, htB, hst, han⟩ := stack_pair_parser_failure (assemble table initial) A src dst hne
    (.at q .entry) (.at q .p1) (.at q .p2) (.at q .p3) (.at next .entry) (.halt failure)
    (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht]) (by simp [assemble, ht])
    cfg hs ha w hw hbad
  exact ⟨t, htB, han, hst⟩

lemma StackProgram.exec_halted {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (cfg : StackConfig Q r) (b : Bool) (ha : cfg.answer = some b) (t : ℕ) : P.exec A cfg t = cfg := by
  induction t with
  | zero => rfl
  | succ t ih => rw [P.exec_succ, ih]; simp [StackProgram.step, ha]

lemma assemble_failure_halts {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r) (initial : Q)
    (A : Language) (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (b : Bool) (hs : cfg.state = .halt b) (ha : cfg.answer = none) :
    ((assemble table initial).step A cfg).answer = some b := by
  simp [StackProgram.step, hs, ha, assemble]

end APSCounting893.Main
end Component_42

section Component_43

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma trailing_finish_queries {k : ℕ} (A : Language) (cfg : TrailingConfig k)
    (earlier : Prop) [Decidable earlier]
    (hs : cfg.state = .at (if earlier then .askE else .askF) .entry) (ha : cfg.answer = none) :
    ∃ b : Bool, ((trailingBaseProgram k).exec A cfg 3).answer = some b ∧
      (b = true ↔ (¬ earlier ∨ ¬ A (cfg.regs (trailingRegIndex .queryE))) ∧
        ¬ A (cfg.regs (trailingRegIndex .queryF))) := by
  classical
  let P := trailingBaseProgram k
  have hquery (cfg' : TrailingConfig k) (hans : cfg'.answer = none)
      (q yes no : TrailingSite k) (reg : Fin (Fintype.card (TrailingReg k) + 2))
      (ht : trailingTable k q = .query reg yes no) (hst : cfg'.state = .at q .entry) :
      P.step A cfg' =
      { state := (if A (cfg'.regs reg) then .at yes .entry else .at no .entry),
        regs := Function.update cfg'.regs reg [], answer := none } := by
    exact assemble_query (trailingTable k) .outerPair q yes no A reg ht cfg' hst hans
  have hhalt (cfg' : TrailingConfig k) (hans : cfg'.answer = none) (b : Bool)
      (hst : cfg'.state = .at (if b then .accept else .reject) .entry) :
      P.step A cfg' = { cfg' with answer := some b } := by
    cases b <;> apply assemble_halt (trailingTable k) .outerPair _ A _ (by rfl) cfg' hst hans
  by_cases he : earlier
  · have hsE : cfg.state = .at .askE .entry := by simpa only [if_pos he] using hs
    let C : TrailingConfig k :=
      { state := if A (cfg.regs (trailingRegIndex .queryE)) then .at .reject .entry else .at .askF .entry,
        regs := Function.update cfg.regs (trailingRegIndex .queryE) [], answer := none }
    have h1 : P.step A cfg = C := hquery cfg ha .askE .reject .askF _ rfl hsE
    by_cases hE : A (cfg.regs (trailingRegIndex .queryE))
    · have h2 : P.step A C = { C with answer := some false } :=
        hhalt C rfl false (by simp [C, hE])
      refine ⟨false, ?_, by simp [he, hE]⟩
      change (P.step A (P.step A (P.step A cfg))).answer = some false
      rw [h1, h2]
      simp [StackProgram.step]
    · let D : TrailingConfig k :=
        { state := if A (cfg.regs (trailingRegIndex .queryF)) then .at .reject .entry else .at .accept .entry,
          regs := Function.update C.regs (trailingRegIndex .queryF) [], answer := none }
      have h2 : P.step A C = D := by
        have hh := hquery C rfl .askF .reject .accept (trailingRegIndex .queryF) rfl (by simp [C, hE])
        simpa only [C, Function.update_of_ne (by simp : trailingRegIndex (k := k) .queryF ≠ trailingRegIndex .queryE)] using hh
      by_cases hF : A (cfg.regs (trailingRegIndex .queryF))
      · have h3 : P.step A D = { D with answer := some false } := hhalt D rfl false (by simp [D, hF])
        refine ⟨false, ?_, by simp [he, hE, hF]⟩
        change (P.step A (P.step A (P.step A cfg))).answer = some false
        rw [h1, h2, h3]
      · have h3 : P.step A D = { D with answer := some true } := hhalt D rfl true (by simp [D, hF])
        refine ⟨true, ?_, by simp [he, hE, hF]⟩
        change (P.step A (P.step A (P.step A cfg))).answer = some true
        rw [h1, h2, h3]
  · have hsF : cfg.state = .at .askF .entry := by simpa only [if_neg he] using hs
    let C : TrailingConfig k :=
      { state := if A (cfg.regs (trailingRegIndex .queryF)) then .at .reject .entry else .at .accept .entry,
        regs := Function.update cfg.regs (trailingRegIndex .queryF) [], answer := none }
    have h1 : P.step A cfg = C := hquery cfg ha .askF .reject .accept _ rfl hsF
    by_cases hF : A (cfg.regs (trailingRegIndex .queryF))
    · have h2 : P.step A C = { C with answer := some false } := hhalt C rfl false (by simp [C, hF])
      refine ⟨false, ?_, by simp [he, hF]⟩
      change (P.step A (P.step A (P.step A cfg))).answer = some false
      rw [h1, h2]
      simp [StackProgram.step]
    · have h2 : P.step A C = { C with answer := some true } := hhalt C rfl true (by simp [C, hF])
      refine ⟨true, ?_, by simp [he, hF]⟩
      change (P.step A (P.step A (P.step A cfg))).answer = some true
      rw [h1, h2]
      simp [StackProgram.step]

end APSCounting893.Main
end Component_43

section Component_44

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma trailing_post_universal {k : ℕ} (A : Language) (cfg : TrailingConfig k)
    (hs : cfg.state = .at (.build .earlier .bitFirst) .entry) (ha : cfg.answer = none) (hc : TrailingClean cfg)
    (x : Word) (e a : Fin (k + 1) →₀ ℕ) (qE qF N : ℕ)
    (hx : x.length ≤ N) (hqe : qE.bits.length ≤ N) (hqf : qF.bits.length ≤ N)
    (hbitsE : cfg.regs (trailingRegIndex .qE) = qE.bits.reverse)
    (hbitsF : cfg.regs (trailingRegIndex .qF) = qF.bits.reverse)
    (hfieldsE : ∀ i, cfg.regs (trailingRegIndex (.eField i)) = (e i).bits.reverse)
    (hfieldsA : ∀ i, cfg.regs (trailingRegIndex (.aField i)) = (a i).bits.reverse)
    (hBE : ∀ i, (e i).bits.length ≤ N) (hBA : ∀ i, (a i).bits.length ≤ N)
    (hp : cfg.regs (trailingRegIndex .inputPrefix) = encodeNat x.length ++ x)
    (hEempty : cfg.regs (trailingRegIndex .queryE) = []) (hFempty : cfg.regs (trailingRegIndex .queryF) = [])
    (hl : cfg.regs (trailingRegIndex .leftClone) = []) (hr : cfg.regs (trailingRegIndex .rightClone) = []) :
    ∃ t ≤ 300 * (k + 2) * (N + 1), ∃ b : Bool,
      ((trailingBaseProgram k).exec A cfg t).answer = some b ∧
      (b = true ↔ (¬ List.Lex (· < ·) (trailingSuffix e 0) (trailingSuffix a 0) ∨
        ¬ A (coefficientQuery x e .numerator qE)) ∧
        ¬ A (coefficientQuery x (orderExponent (List.ofFn (fun i : Fin k => i.castSucc)) a) .numerator qF)) := by
  classical
  let af := orderExponent (List.ofFn (fun i : Fin k => i.castSucc)) a
  obtain ⟨t, ht, hex⟩ := trailing_build_two_queries A cfg hs ha hc x e a qE qF N hx hqe hqf
    hbitsE hbitsF hfieldsE hfieldsA hBE hBA hp hEempty hFempty
  let C : TrailingConfig k :=
    { state := .at (.compareBegin 0) .entry,
      regs := Function.update (Function.update cfg.regs (trailingRegIndex .queryE) (coefficientQuery x e .numerator qE))
        (trailingRegIndex .queryF) (coefficientQuery x af .numerator qF), answer := none }
  have hex' : (trailingBaseProgram k).exec A cfg t = C := hex
  have hv : ∀ i : Fin (k + 1), 0 ≤ i.val →
      C.regs (trailingRegIndex (.eField i)) = (e i).bits.reverse ∧
      C.regs (trailingRegIndex (.aField i)) = (a i).bits.reverse := by
    intro i hi
    constructor
    · simpa [C] using hfieldsE i
    · simpa [C] using hfieldsA i
  obtain ⟨s, hsB, D, heD, hstD, hanD, hframeD⟩ := trailing_compare_loop A e a N k 0 (by omega)
    (by intro i; exact ⟨hBE i, hBA i⟩) C rfl rfl hv
    (by simpa [C] using hc.tmp) (by simpa [C] using hc.scratch)
    (by simpa [C] using hl) (by simpa [C] using hr)
  have hsafeE : TrailingCompareSafe (trailingRegIndex (k := k) .queryE) := by
    constructor
    · simp
    constructor
    · simp
    intro i
    simp
  have hsafeF : TrailingCompareSafe (trailingRegIndex (k := k) .queryF) := by
    constructor
    · simp
    constructor
    · simp
    intro i
    simp
  have hqueryE : D.regs (trailingRegIndex .queryE) = coefficientQuery x e .numerator qE := by
    rw [hframeD _ hsafeE]
    simp [C]
  have hqueryF : D.regs (trailingRegIndex .queryF) = coefficientQuery x af .numerator qF := by
    rw [hframeD _ hsafeF]
    simp [C]
  obtain ⟨b, hans, hiff⟩ := trailing_finish_queries A D
    (List.Lex (· < ·) (trailingSuffix e 0) (trailingSuffix a 0)) hstD hanD
  refine ⟨t + s + 3, ?_, b, ?_, ?_⟩
  · nlinarith
  · rw [StackProgram.exec_add, StackProgram.exec_add, hex', heD]
    exact hans
  · simpa only [hqueryE, hqueryF, af] using hiff

end APSCounting893.Main
end Component_44

section Component_45

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma assemble_nat_sequence {Q : Type} [Fintype Q] {r d : ℕ}
    (table : Q → WordOp Q r) (initial : Q) (A : Language)
    (src counter : Fin (r + 2)) (hsc : src ≠ counter)
    (reg : Fin d → Fin (r + 2)) (hinj : Function.Injective reg)
    (hrs : ∀ i, reg i ≠ src) (hrc : ∀ i, reg i ≠ counter)
    (site : Fin (d + 1) → Q) (failure : Bool)
    (htable : ∀ i : Fin d, table (site i.castSucc) = .nat src counter (reg i) (site i.succ) failure)
    (ns : List ℕ) (offset B : ℕ) (hsize : offset + ns.length ≤ d)
    (hB : ∀ n ∈ ns, n.bits.length ≤ B)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at (site ⟨offset, by omega⟩) .entry) (ha : cfg.answer = none)
    (rest : Word) (hw : cfg.regs src = ns.flatMap encodeNat ++ rest)
    (hc : cfg.regs counter = [])
    (hempty : ∀ i : Fin d, offset ≤ i.val → i.val < offset + ns.length → cfg.regs (reg i) = []) :
    ∃ t ≤ ns.length * (5 * B + 3), ∃ out,
      (assemble table initial).exec A cfg t = out ∧
      out.state = .at (site ⟨offset + ns.length, by omega⟩) .entry ∧ out.answer = none ∧
      out.regs src = rest ∧ out.regs counter = [] ∧
      (∀ i : Fin ns.length, out.regs (reg ⟨offset + i.val, by omega⟩) = ns[i].bits.reverse) ∧
      (∀ j, j ≠ src → (∀ i : Fin d, offset ≤ i.val → i.val < offset + ns.length → j ≠ reg i) →
        out.regs j = cfg.regs j) := by
  classical
  induction ns generalizing offset cfg with
  | nil =>
      refine ⟨0, by simp, cfg, rfl, ?_, ha, ?_, hc, ?_, ?_⟩
      · simpa using hs
      · simpa using hw
      · intro i; exact Fin.elim0 i
      · intro j hj hr; rfl
  | cons n ns ih =>
      let i0 : Fin d := ⟨offset, by simpa using (show offset < d by simp only [List.length_cons] at hsize; omega)⟩
      let cfg1 : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r :=
        { state := .at (site ⟨offset + 1, by simp only [List.length_cons] at hsize; omega⟩) .entry,
          regs := Function.update (Function.update (Function.update cfg.regs src (ns.flatMap encodeNat ++ rest)) counter [])
            (reg i0) n.bits.reverse, answer := none }
      have hstep : (assemble table initial).exec A cfg (5 * n.bits.length + 3) = cfg1 := by
        apply assemble_nat table initial (site i0.castSucc) (site i0.succ) A src counter (reg i0)
          hsc (hrs i0).symm (hrc i0).symm failure (htable i0) cfg hs ha n (ns.flatMap encodeNat ++ rest) _ hc
          (hempty i0 le_rfl (by simp [i0]))
        simpa only [List.flatMap_cons, List.append_assoc] using hw
      have hw1 : cfg1.regs src = ns.flatMap encodeNat ++ rest := by simp [cfg1, hsc, (hrs i0).symm]
      have hc1 : cfg1.regs counter = [] := by simp [cfg1, (hrc i0).symm]
      have hempty1 : ∀ i : Fin d, offset + 1 ≤ i.val → i.val < offset + 1 + ns.length → cfg1.regs (reg i) = [] := by
        intro i hlo hhi
        have hne : reg i ≠ reg i0 := by intro he; have hh := congrArg Fin.val (hinj he); change i.val = offset at hh; omega
        simp only [cfg1, Function.update_of_ne hne, Function.update_of_ne (hrc i), Function.update_of_ne (hrs i)]
        exact hempty i (by omega) (by simp only [List.length_cons]; omega)
      obtain ⟨t, ht, out, he, hstate, hans, hsrc, hcounter, hdata, hframe⟩ :=
        ih (offset + 1) (by simp only [List.length_cons] at hsize; omega)
          (by intro m hm; exact hB m (List.mem_cons_of_mem n hm)) cfg1 rfl rfl hw1 hc1 hempty1
      refine ⟨(5 * n.bits.length + 3) + t, ?_, out, ?_, ?_, hans, hsrc, hcounter, ?_, ?_⟩
      · have hn := hB n (by simp)
        simp only [List.length_cons]
        nlinarith
      · rw [StackProgram.exec_add, hstep, he]
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstate
      · intro j
        by_cases hj : j.val = 0
        · have hreg0 : reg ⟨offset + j.val, by omega⟩ = reg i0 := by congr 1; apply Fin.ext; simp [i0, hj]
          rw [hreg0, hframe (reg i0) (hrs i0)]
          · simp [cfg1, hj]
          · intro i hlo hhi hi
            have hval := congrArg Fin.val (hinj hi)
            change offset = i.val at hval
            omega
        · let j' : Fin ns.length := ⟨j.val - 1, by have hh := j.isLt; simp only [List.length_cons] at hh; omega⟩
          have hval : offset + 1 + j'.val = offset + j.val := by simp only [j']; omega
          have hh := hdata j'
          have hregEq : reg ⟨offset + 1 + j'.val, by omega⟩ = reg ⟨offset + j.val, by omega⟩ := by congr 1; exact Fin.ext hval
          rw [hregEq] at hh
          change out.regs (reg ⟨offset + j.val, by omega⟩) = (n :: ns)[j.val].bits.reverse
          change out.regs (reg ⟨offset + j.val, by omega⟩) = ns[j.val - 1].bits.reverse at hh
          simpa only [List.getElem_cons, hj, if_false, dite_false] using hh
      · intro j hjs hjreg
        rw [hframe j hjs (by intro i hlo hhi; apply hjreg i (by omega); simp only [List.length_cons]; omega)]
        have hj0 := hjreg i0 le_rfl (by simp [i0])
        simp only [cfg1, Function.update_of_ne hj0]
        by_cases hjc : j = counter
        · subst j
          simp only [Function.update_self, hc]
        · simp only [Function.update_of_ne hjc, Function.update_of_ne hjs]

end APSCounting893.Main
end Component_45

section Component_46

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma decodeNats_code (ns : List ℕ) (rest : Word) :
    decodeNats ns.length (ns.flatMap encodeNat ++ rest) = some (ns, rest) := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decodeNats,
        decodeNat_code, Option.bind_eq_bind, Option.bind_some, Option.pure_def, ih]

lemma exponentOfList_ofFn {k : ℕ} (a : Fin (k + 1) →₀ ℕ) :
    exponentOfList k (List.ofFn (fun i => a i)) = a := by
  ext i
  simp only [exponentOfList, Finsupp.onFinset_apply, List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]

lemma decodeExponent_code {k : ℕ} (a : Fin (k + 1) →₀ ℕ) (rest : Word) :
    decodeExponent k (encodeExponent a ++ rest) = some (a, rest) := by
  have hns := decodeNats_code (List.ofFn (fun i => a i)) rest
  simp only [List.length_ofFn] at hns
  simp only [decodeExponent, encodeExponent, encodeList, List.length_ofFn, List.append_assoc, decodeNat_code,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, if_pos rfl, ite_true, hns, exponentOfList_ofFn]

lemma decodeExistential_code {k : ℕ} (a : Fin (k + 1) →₀ ℕ) (q : ℕ) (pad : Word) :
    decodeExistential k (encodeExistential a q ++ pad) = some (a, q) := by
  simp only [decodeExistential, encodeExistential, List.append_assoc, decodeExponent_code,
    decodeNat_code, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

lemma decodeUniversal_code {k : ℕ} (e : Fin (k + 1) →₀ ℕ) (qE qF : ℕ) (pad : Word) :
    decodeUniversal k (encodeUniversal e qE qF ++ pad) = some (e, qE, qF) := by
  simp only [decodeUniversal, encodeUniversal, List.append_assoc, decodeExponent_code,
    decodeNat_code, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

lemma baseTrailing_pair {k : ℕ} (rho : CoefficientRepresentation k)
    (x aWord u : Word) :
    BaseTrailingLanguage rho (pairWord (pairWord x aWord) u) =
      (match decodeExistential k aWord with
      | none => False
      | some (a, qA) => CoefficientBitLanguage rho (coefficientQuery x a .numerator qA) ∧
          match decodeUniversal k u with
          | none => True
          | some (e, qE, qF) =>
              (¬ List.Lex (· < ·)
                ((List.ofFn (fun i : Fin k => i.castSucc)).map (fun v => e v))
                ((List.ofFn (fun i : Fin k => i.castSucc)).map (fun v => a v)) ∨
                ¬ CoefficientBitLanguage rho (coefficientQuery x e .numerator qE)) ∧
              ¬ CoefficientBitLanguage rho (coefficientQuery x
                (orderExponent (List.ofFn (fun i : Fin k => i.castSucc)) a) .numerator qF)) := by
  simp only [BaseTrailingLanguage, decodePair_pairWord] <;> rfl

lemma decodeNats_inverse (n : ℕ) (w : Word) (ns : List ℕ) (rest : Word)
    (h : decodeNats n w = some (ns, rest)) : ns.length = n ∧ w = ns.flatMap encodeNat ++ rest := by
  induction n generalizing w ns rest with
  | zero =>
      have heq : ([], w) = (ns, rest) := by simpa [decodeNats] using h
      cases heq
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      cases ha : decodeNat w with
      | none => simp [decodeNats, ha] at h
      | some p =>
          cases hr : decodeNats n p.2 with
          | none => simp [decodeNats, ha, hr] at h
          | some q =>
              have heq : (p.1 :: q.1, q.2) = (ns, rest) := by simpa [decodeNats, ha, hr] using h
              cases heq
              obtain ⟨hlen, hword⟩ := ih p.2 q.1 q.2 hr
              constructor
              · simp [hlen]
              · rw [decodeNat_inverse w p.1 p.2 ha, hword]
                simp [List.append_assoc]

lemma ofFn_exponentOfList (k : ℕ) (ns : List ℕ) (h : ns.length = k + 1) :
    List.ofFn (fun i => exponentOfList k ns i) = ns := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro i hi hi'
    simp only [List.getElem_ofFn, exponentOfList, Finsupp.onFinset_apply]
    rw [List.getElem?_eq_getElem hi']
    rfl

lemma decodeExponent_inverse (k : ℕ) (w : Word) (a : Fin (k + 1) →₀ ℕ) (rest : Word)
    (h : decodeExponent k w = some (a, rest)) : w = encodeExponent a ++ rest := by
  cases hn : decodeNat w with
  | none => simp [decodeExponent, hn] at h
  | some p =>
      by_cases hp : p.1 = k + 1
      · cases hns : decodeNats (k + 1) p.2 with
        | none => simp [decodeExponent, hn, hp, hns] at h
        | some q =>
            have heq : (exponentOfList k q.1, q.2) = (a, rest) := by
              simpa [decodeExponent, hn, hp, hns] using h
            cases heq
            obtain ⟨hlen, hword⟩ := decodeNats_inverse (k + 1) p.2 q.1 q.2 hns
            rw [decodeNat_inverse w p.1 p.2 hn, hword]
            simp only [encodeExponent, encodeList, ofFn_exponentOfList k q.1 hlen,
              hlen, hp, List.append_assoc]
      · simp [decodeExponent, hn, hp] at h

end APSCounting893.Main
end Component_46

section Component_47

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma assemble_nat_sequence_failure {Q : Type} [Fintype Q] {r d : ℕ}
    (table : Q → WordOp Q r) (initial : Q) (A : Language)
    (src counter : Fin (r + 2)) (hsc : src ≠ counter)
    (reg : Fin d → Fin (r + 2)) (hinj : Function.Injective reg)
    (hrs : ∀ i, reg i ≠ src) (hrc : ∀ i, reg i ≠ counter)
    (site : Fin (d + 1) → Q) (failure : Bool)
    (htable : ∀ i : Fin d, table (site i.castSucc) = .nat src counter (reg i) (site i.succ) failure)
    (count offset W : ℕ) (hsize : offset + count ≤ d)
    (cfg : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r)
    (hs : cfg.state = .at (site ⟨offset, by omega⟩) .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) (hW : w.length ≤ W)
    (hc : cfg.regs counter = [])
    (hempty : ∀ i : Fin d, offset ≤ i.val → i.val < offset + count → cfg.regs (reg i) = [])
    (hbad : decodeNats count w = none) :
    ∃ t ≤ count * (5 * W + 3), ((assemble table initial).exec A cfg t).answer = none ∧
      ((assemble table initial).exec A cfg t).state = .halt failure := by
  classical
  induction count generalizing offset cfg w with
  | zero => simp [decodeNats] at hbad
  | succ count ih =>
      let i0 : Fin d := ⟨offset, by omega⟩
      cases hn : decodeNat w with
      | none =>
          obtain ⟨t, ht, ha, hs⟩ := assemble_nat_failure table initial (site i0.castSucc) (site i0.succ) A
            src counter (reg i0) hsc (hrs i0).symm (hrc i0).symm failure (htable i0)
            cfg hs ha w hw hc (hempty i0 le_rfl (by simp [i0])) hn
          exact ⟨t, by nlinarith, ha, hs⟩
      | some pair =>
          rcases pair with ⟨n, rest⟩
          have hword := decodeNat_inverse w n rest hn
          have hrest : rest.length ≤ W := by
            have hh := congrArg List.length hword
            simp only [List.length_append] at hh
            omega
          have htail : decodeNats count rest = none := by
            cases ht : decodeNats count rest with
            | none => rfl
            | some pair => simp [decodeNats, hn, ht] at hbad
          have hnB : n.bits.length ≤ W := by
            have hh := congrArg List.length hword
            simp only [List.length_append, encodeNat, List.length_replicate, List.length_singleton] at hh
            omega
          let cfg1 : StackConfig (AssemblyControl Q (assemblyConstantBound table)) r :=
            { state := .at (site ⟨offset + 1, by omega⟩) .entry,
              regs := Function.update (Function.update (Function.update cfg.regs src rest) counter [])
                (reg i0) n.bits.reverse, answer := none }
          have hstep : (assemble table initial).exec A cfg (5 * n.bits.length + 3) = cfg1 := by
            exact assemble_nat table initial (site i0.castSucc) (site i0.succ) A src counter (reg i0)
              hsc (hrs i0).symm (hrc i0).symm failure (htable i0) cfg hs ha n rest (hw.trans hword)
              hc (hempty i0 le_rfl (by simp [i0]))
          have hw1 : cfg1.regs src = rest := by simp [cfg1, hsc, (hrs i0).symm]
          have hc1 : cfg1.regs counter = [] := by simp [cfg1, (hrc i0).symm]
          have hempty1 : ∀ i : Fin d, offset + 1 ≤ i.val → i.val < offset + 1 + count → cfg1.regs (reg i) = [] := by
            intro i hlo hhi
            have hne : reg i ≠ reg i0 := by intro he; have hh := congrArg Fin.val (hinj he); change i.val = offset at hh; omega
            simp only [cfg1, Function.update_of_ne hne, Function.update_of_ne (hrc i), Function.update_of_ne (hrs i)]
            exact hempty i (by omega) (by omega)
          obtain ⟨t, ht, ha1, hs1⟩ := ih (offset + 1) (by omega) cfg1 rfl rfl rest hw1 hrest hc1 hempty1 htail
          refine ⟨(5 * n.bits.length + 3) + t, by nlinarith, ?_⟩
          rw [StackProgram.exec_add, hstep]
          exact ⟨ha1, hs1⟩

end APSCounting893.Main
end Component_47

section Component_48

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def trailingParseSource {k : ℕ} (isA : Bool) : Fin (Fintype.card (TrailingReg k) + 2) :=
  if isA then trailingRegIndex .inner else 0

noncomputable def trailingParseReg {k : ℕ} (isA : Bool) (i : Fin (k + 1)) :
    Fin (Fintype.card (TrailingReg k) + 2) :=
  if isA then trailingRegIndex (.aField i) else trailingRegIndex (.eField i)

def trailingParseSite {k : ℕ} (isA : Bool) (i : Fin (k + 2)) : TrailingSite k :=
  if h : i.val < k + 1 then
    if isA then .aField ⟨i.val, h⟩ else .eField ⟨i.val, h⟩
  else if isA then .aBit else .eBit

lemma trailingParseReg_injective (k : ℕ) (isA : Bool) : Function.Injective (@trailingParseReg k isA) := by
  intro i j h
  cases isA <;> simpa [trailingParseReg] using h

lemma trailingParseReg_ne_source {k : ℕ} (isA : Bool) (i : Fin (k + 1)) :
    trailingParseReg isA i ≠ trailingParseSource isA := by
  cases isA <;> simp [trailingParseReg, trailingParseSource]

lemma trailingParseReg_ne_counter {k : ℕ} (isA : Bool) (i : Fin (k + 1)) :
    trailingParseReg isA i ≠ trailingRegIndex .natCount := by
  cases isA <;> simp [trailingParseReg]

lemma trailingParseSource_ne_counter {k : ℕ} (isA : Bool) :
    trailingParseSource (k := k) isA ≠ trailingRegIndex .natCount := by
  cases isA <;> simp [trailingParseSource, Ne.symm (trailingRegIndex_ne_zero _)]

lemma trailingParse_transition {k : ℕ} (isA : Bool) (i : Fin (k + 1)) :
    trailingTable k (trailingParseSite isA i.castSucc) =
      .nat (trailingParseSource isA) (trailingRegIndex .natCount) (trailingParseReg isA i)
        (trailingParseSite isA i.succ) (!isA) := by
  cases isA <;>
    simp [trailingParseSite, trailingParseReg, trailingParseSource, trailingTable,
      trailingNextA, trailingNextE, i.isLt, Fin.ext_iff]

lemma trailing_parse_fields {k : ℕ} (A : Language) (isA : Bool) (cfg : StackConfig
    (AssemblyControl (TrailingSite k) (assemblyConstantBound (trailingTable k))) (Fintype.card (TrailingReg k)))
    (hs : cfg.state = .at (trailingParseSite isA 0) .entry) (ha : cfg.answer = none)
    (e : Fin (k + 1) →₀ ℕ) (rest : Word) (B : ℕ)
    (hw : cfg.regs (trailingParseSource isA) = (List.ofFn (fun i => e i)).flatMap encodeNat ++ rest)
    (hc : cfg.regs (trailingRegIndex .natCount) = [])
    (hempty : ∀ i, cfg.regs (trailingParseReg isA i) = [])
    (hB : ∀ i, (e i).bits.length ≤ B) :
    ∃ t ≤ (k + 1) * (5 * B + 3), ∃ out,
      (trailingBaseProgram k).exec A cfg t = out ∧
      out.state = .at (if isA then .aBit else .eBit) .entry ∧ out.answer = none ∧
      out.regs (trailingParseSource isA) = rest ∧ out.regs (trailingRegIndex .natCount) = [] ∧
      (∀ i, out.regs (trailingParseReg isA i) = (e i).bits.reverse) ∧
      (∀ j, j ≠ trailingParseSource isA → (∀ i, j ≠ trailingParseReg isA i) → out.regs j = cfg.regs j) := by
  classical
  let ns := List.ofFn (fun i => e i)
  have hn : ns.length = k + 1 := List.length_ofFn
  obtain ⟨t, ht, out, he, hst, han, hsrc, hcounter, hdata, hframe⟩ :=
    assemble_nat_sequence (trailingTable k) .outerPair A (trailingParseSource isA) (trailingRegIndex .natCount)
      (trailingParseSource_ne_counter isA) (trailingParseReg isA) (trailingParseReg_injective k isA)
      (trailingParseReg_ne_source isA) (trailingParseReg_ne_counter isA)
      (trailingParseSite isA) (!isA) (trailingParse_transition isA) ns 0 B (by simp [ns])
      (by intro n hn; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hn; exact hB i)
      cfg hs ha rest hw hc (by intro i hlo hhi; exact hempty i)
  refine ⟨t, by simpa only [hn] using ht, out, he, ?_, han, hsrc, hcounter, ?_, ?_⟩
  · simpa [trailingParseSite, hn] using hst
  · intro i
    let j : Fin ns.length := ⟨i.val, by rw [hn]; exact i.isLt⟩
    have hh := hdata j
    have hidx : (⟨0 + j.val, by omega⟩ : Fin (k + 1)) = i := Fin.ext (by simp [j])
    rw [hidx] at hh
    change out.regs (trailingParseReg isA i) = ns[i.val].bits.reverse at hh
    simpa only [ns, List.getElem_ofFn] using hh
  · intro j hjs hjreg
    exact hframe j hjs (by intro i hlo hhi; exact hjreg i)

lemma trailing_parse_fields_failure {k : ℕ} (A : Language) (isA : Bool) (cfg : StackConfig
    (AssemblyControl (TrailingSite k) (assemblyConstantBound (trailingTable k))) (Fintype.card (TrailingReg k)))
    (hs : cfg.state = .at (trailingParseSite isA 0) .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs (trailingParseSource isA) = w)
    (hc : cfg.regs (trailingRegIndex .natCount) = [])
    (hempty : ∀ i, cfg.regs (trailingParseReg isA i) = [])
    (hbad : decodeNats (k + 1) w = none) :
    ∃ t ≤ (k + 1) * (5 * w.length + 3), ((trailingBaseProgram k).exec A cfg t).answer = none ∧
      ((trailingBaseProgram k).exec A cfg t).state = .halt (!isA) := by
  exact assemble_nat_sequence_failure (trailingTable k) .outerPair A
    (trailingParseSource isA) (trailingRegIndex .natCount) (trailingParseSource_ne_counter isA)
    (trailingParseReg isA) (trailingParseReg_injective k isA)
    (trailingParseReg_ne_source isA) (trailingParseReg_ne_counter isA)
    (trailingParseSite isA) (!isA) (trailingParse_transition isA) (k + 1) 0 w.length (by omega)
    cfg hs ha w hw le_rfl hc (by intro i hlo hhi; exact hempty i) hbad

end APSCounting893.Main
end Component_48

section Component_49

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stripWord_inverse (word input rest : Word) (h : stripWord word input = some rest) :
    input = word ++ rest := by
  induction word generalizing input with
  | nil => simpa [stripWord] using h
  | cons b word ih =>
      cases input with
      | nil => simp [stripWord] at h
      | cons c input =>
          by_cases he : b = c
          · subst c
            have ht : stripWord word input = some rest := by simpa [stripWord] using h
            simpa using congrArg (List.cons b) (ih input ht)
          · simp [stripWord, he] at h

def trailingParsePrefix {k : ℕ} (isA : Bool) : TrailingSite k := if isA then .aPrefix else .uPrefix

lemma trailingParsePrefix_transition {k : ℕ} (isA : Bool) :
    trailingTable k (trailingParsePrefix isA) = .check (trailingParseSource isA)
      (encodeNat (k + 1)) (trailingParseSite isA 0) (!isA) := by
  cases isA <;> simp [trailingParsePrefix, trailingParseSource, trailingParseSite, trailingTable]

lemma trailing_parse_exponent {k : ℕ} (A : Language) (isA : Bool) (cfg : StackConfig
    (AssemblyControl (TrailingSite k) (assemblyConstantBound (trailingTable k))) (Fintype.card (TrailingReg k)))
    (hs : cfg.state = .at (trailingParsePrefix isA) .entry) (ha : cfg.answer = none)
    (e : Fin (k + 1) →₀ ℕ) (rest : Word) (B : ℕ)
    (hw : cfg.regs (trailingParseSource isA) = encodeExponent e ++ rest)
    (hc : cfg.regs (trailingRegIndex .natCount) = [])
    (hempty : ∀ i, cfg.regs (trailingParseReg isA i) = [])
    (hB : ∀ i, (e i).bits.length ≤ B) :
    ∃ t ≤ (encodeNat (k + 1)).length + 2 + (k + 1) * (5 * B + 3), ∃ out,
      (trailingBaseProgram k).exec A cfg t = out ∧
      out.state = .at (if isA then .aBit else .eBit) .entry ∧ out.answer = none ∧
      out.regs (trailingParseSource isA) = rest ∧ out.regs (trailingRegIndex .natCount) = [] ∧
      (∀ i, out.regs (trailingParseReg isA i) = (e i).bits.reverse) ∧
      (∀ j, j ≠ trailingParseSource isA → (∀ i, j ≠ trailingParseReg isA i) → out.regs j = cfg.regs j) := by
  classical
  let body := (List.ofFn (fun i => e i)).flatMap encodeNat ++ rest
  have hword : cfg.regs (trailingParseSource isA) = encodeNat (k + 1) ++ body := by
    simpa only [encodeExponent, encodeList, List.length_ofFn, List.append_assoc] using hw
  obtain ⟨t, ht, han, hres⟩ := assemble_check (trailingTable k) .outerPair (trailingParsePrefix isA)
    (trailingParseSite isA 0) A (trailingParseSource isA) (encodeNat (k + 1)) (!isA)
    (trailingParsePrefix_transition isA) cfg hs ha _ hword
  rw [stripWord_prefix] at hres
  let cfg1 := (trailingBaseProgram k).exec A cfg t
  have hs1 : cfg1.state = .at (trailingParseSite isA 0) .entry := hres.1
  have ha1 : cfg1.answer = none := han
  have hr1 : cfg1.regs = Function.update cfg.regs (trailingParseSource isA) body := hres.2
  have hw1 : cfg1.regs (trailingParseSource isA) = body := by rw [hr1]; simp
  have hc1 : cfg1.regs (trailingRegIndex .natCount) = [] := by
    rw [hr1, Function.update_of_ne (trailingParseSource_ne_counter isA).symm, hc]
  have he1 : ∀ i, cfg1.regs (trailingParseReg isA i) = [] := by
    intro i
    rw [hr1, Function.update_of_ne (trailingParseReg_ne_source isA i), hempty i]
  obtain ⟨s, hsB, out, he, hst, hans, hsrc, hcounter, hdata, hframe⟩ :=
    trailing_parse_fields A isA cfg1 hs1 ha1 e rest B hw1 hc1 he1 hB
  refine ⟨t + s, by omega, out, ?_, hst, hans, hsrc, hcounter, hdata, ?_⟩
  · rw [StackProgram.exec_add]
    exact he
  · intro j hjs hjreg
    rw [hframe j hjs hjreg, hr1, Function.update_of_ne hjs]

end APSCounting893.Main
end Component_49

section Component_50

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma trailing_parse_exponent_failure {k : ℕ} (A : Language) (isA : Bool) (cfg : StackConfig
    (AssemblyControl (TrailingSite k) (assemblyConstantBound (trailingTable k))) (Fintype.card (TrailingReg k)))
    (hs : cfg.state = .at (trailingParsePrefix isA) .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs (trailingParseSource isA) = w)
    (hc : cfg.regs (trailingRegIndex .natCount) = [])
    (hempty : ∀ i, cfg.regs (trailingParseReg isA i) = [])
    (hbad : decodeExponent k w = none) :
    ∃ t ≤ (encodeNat (k + 1)).length + 2 + (k + 1) * (5 * w.length + 3),
      ((trailingBaseProgram k).exec A cfg t).answer = none ∧
      ((trailingBaseProgram k).exec A cfg t).state = .halt (!isA) := by
  classical
  obtain ⟨t, ht, han, hres⟩ := assemble_check (trailingTable k) .outerPair (trailingParsePrefix isA)
    (trailingParseSite isA 0) A (trailingParseSource isA) (encodeNat (k + 1)) (!isA)
    (trailingParsePrefix_transition isA) cfg hs ha w hw
  cases hstrip : stripWord (encodeNat (k + 1)) w with
  | none =>
      rw [hstrip] at hres
      exact ⟨t, by omega, han, hres⟩
  | some body =>
      rw [hstrip] at hres
      have hwcode := stripWord_inverse (encodeNat (k + 1)) w body hstrip
      have htailbad : decodeNats (k + 1) body = none := by
        cases hb : decodeNats (k + 1) body with
        | none => rfl
        | some pair => simp [decodeExponent, hwcode, decodeNat_code, hb] at hbad
      let cfg1 := (trailingBaseProgram k).exec A cfg t
      have hs1 : cfg1.state = .at (trailingParseSite isA 0) .entry := hres.1
      have ha1 : cfg1.answer = none := han
      have hr1 : cfg1.regs = Function.update cfg.regs (trailingParseSource isA) body := hres.2
      have hw1 : cfg1.regs (trailingParseSource isA) = body := by rw [hr1]; simp
      have hc1 : cfg1.regs (trailingRegIndex .natCount) = [] := by
        rw [hr1, Function.update_of_ne (trailingParseSource_ne_counter isA).symm, hc]
      have he1 : ∀ i, cfg1.regs (trailingParseReg isA i) = [] := by
        intro i
        rw [hr1, Function.update_of_ne (trailingParseReg_ne_source isA i), hempty i]
      obtain ⟨s, hsB, hans, hst⟩ := trailing_parse_fields_failure A isA cfg1 hs1 ha1 body hw1 hc1 he1 htailbad
      have hbody : body.length ≤ w.length := by rw [hwcode, List.length_append]; omega
      refine ⟨t + s, ?_, ?_⟩
      · have hm := Nat.mul_le_mul_left (k + 1) (show 5 * body.length + 3 ≤ 5 * w.length + 3 by omega)
        omega
      · rw [StackProgram.exec_add]
        exact ⟨hans, hst⟩

end APSCounting893.Main
end Component_50

section Component_51

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main

noncomputable def trailingBitSource {k : ℕ} : TrailingQuery → Fin (Fintype.card (TrailingReg k) + 2)
  | .candidate => trailingRegIndex .inner
  | .earlier | .final => 0

def trailingBitParseSite (k : ℕ) : TrailingQuery → TrailingSite k
  | .candidate => .aBit
  | .earlier => .eBit
  | .final => .finalBit

def trailingAfterBitParse (k : ℕ) : TrailingQuery → TrailingSite k
  | .candidate => .copyXForLength
  | .earlier => .finalBit
  | .final => .build .earlier .bitFirst

def trailingParseFailure : TrailingQuery → Bool
  | .candidate => false
  | .earlier | .final => true

lemma trailingBitSource_ne_counter {k : ℕ} (q : TrailingQuery) :
    trailingBitSource (k := k) q ≠ trailingRegIndex .natCount := by
  cases q <;> simp [trailingBitSource, Ne.symm (trailingRegIndex_ne_zero _)]

lemma trailingBitSource_ne_bit {k : ℕ} (q : TrailingQuery) :
    trailingBitSource (k := k) q ≠ trailingBitReg q := by
  cases q <;> simp [trailingBitSource, trailingBitReg, Ne.symm (trailingRegIndex_ne_zero _)]

lemma trailingBitCounter_ne_bit {k : ℕ} (q : TrailingQuery) :
    trailingRegIndex (k := k) .natCount ≠ trailingBitReg q := by
  cases q <;> simp [trailingBitReg]

lemma trailingBitParse_transition {k : ℕ} (q : TrailingQuery) :
    trailingTable k (trailingBitParseSite k q) = .nat (trailingBitSource q)
      (trailingRegIndex .natCount) (trailingBitReg q) (trailingAfterBitParse k q) (trailingParseFailure q) := by
  cases q <;> rfl

lemma trailing_parse_bit {k : ℕ} (A : Language) (q : TrailingQuery) (cfg : TrailingConfig k)
    (hs : cfg.state = .at (trailingBitParseSite k q) .entry) (ha : cfg.answer = none)
    (n : ℕ) (rest : Word) (hw : cfg.regs (trailingBitSource q) = encodeNat n ++ rest)
    (hc : cfg.regs (trailingRegIndex .natCount) = []) (hd : cfg.regs (trailingBitReg q) = []) :
    (trailingBaseProgram k).exec A cfg (5 * n.bits.length + 3) =
      { state := .at (trailingAfterBitParse k q) .entry,
        regs := Function.update (Function.update cfg.regs (trailingBitSource q) rest)
          (trailingBitReg q) n.bits.reverse, answer := none } := by
  have hh := assemble_nat (trailingTable k) .outerPair (trailingBitParseSite k q) (trailingAfterBitParse k q) A
    (trailingBitSource q) (trailingRegIndex .natCount) (trailingBitReg q)
    (trailingBitSource_ne_counter q) (trailingBitSource_ne_bit q) (trailingBitCounter_ne_bit q)
    (trailingParseFailure q) (trailingBitParse_transition q) cfg hs ha n rest hw hc hd
  have hrestore : Function.update (Function.update cfg.regs (trailingBitSource q) rest)
      (trailingRegIndex .natCount) [] = Function.update cfg.regs (trailingBitSource q) rest :=
    update_empty_after_update cfg.regs _ _ rest (trailingBitSource_ne_counter q) hc
  simpa only [trailingBaseProgram, hrestore] using hh

lemma trailing_parse_bit_failure {k : ℕ} (A : Language) (q : TrailingQuery) (cfg : TrailingConfig k)
    (hs : cfg.state = .at (trailingBitParseSite k q) .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs (trailingBitSource q) = w)
    (hc : cfg.regs (trailingRegIndex .natCount) = []) (hd : cfg.regs (trailingBitReg q) = [])
    (hbad : decodeNat w = none) :
    ∃ t ≤ 5 * w.length + 3, ((trailingBaseProgram k).exec A cfg t).answer = none ∧
      ((trailingBaseProgram k).exec A cfg t).state = .halt (trailingParseFailure q) := by
  exact assemble_nat_failure (trailingTable k) .outerPair (trailingBitParseSite k q) (trailingAfterBitParse k q) A
    (trailingBitSource q) (trailingRegIndex .natCount) (trailingBitReg q)
    (trailingBitSource_ne_counter q) (trailingBitSource_ne_bit q) (trailingBitCounter_ne_bit q)
    (trailingParseFailure q) (trailingBitParse_transition q) cfg hs ha w hw hc hd hbad

end APSCounting893.Main
end Component_51

section Component_52

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main

lemma decodeExistential_inverse {k : ℕ} (w : Word) (a : Fin (k + 1) →₀ ℕ) (q : ℕ)
    (h : decodeExistential k w = some (a, q)) : ∃ pad, w = encodeExistential a q ++ pad := by
  cases ha : decodeExponent k w with
  | none => simp [decodeExistential, ha] at h
  | some pair =>
      rcases pair with ⟨a', rest⟩
      cases hq : decodeNat rest with
      | none => simp [decodeExistential, ha, hq] at h
      | some pair =>
          rcases pair with ⟨q', pad⟩
          have heq : (a', q') = (a, q) := by simpa [decodeExistential, ha, hq] using h
          cases heq
          refine ⟨pad, ?_⟩
          rw [decodeExponent_inverse k w a rest ha, decodeNat_inverse rest q pad hq]
          simp only [encodeExistential, List.append_assoc]

lemma decodeUniversal_inverse {k : ℕ} (w : Word) (e : Fin (k + 1) →₀ ℕ) (qE qF : ℕ)
    (h : decodeUniversal k w = some (e, qE, qF)) : ∃ pad, w = encodeUniversal e qE qF ++ pad := by
  cases he : decodeExponent k w with
  | none => simp [decodeUniversal, he] at h
  | some pair =>
      rcases pair with ⟨e', rest⟩
      cases hqe : decodeNat rest with
      | none => simp [decodeUniversal, he, hqe] at h
      | some pair =>
          rcases pair with ⟨qE', rest'⟩
          cases hqf : decodeNat rest' with
          | none => simp [decodeUniversal, he, hqe, hqf] at h
          | some pair =>
              rcases pair with ⟨qF', pad⟩
              have heq : (e', qE', qF') = (e, qE, qF) := by simpa [decodeUniversal, he, hqe, hqf] using h
              cases heq
              refine ⟨pad, ?_⟩
              rw [decodeExponent_inverse k w e rest he, decodeNat_inverse rest qE rest' hqe,
                decodeNat_inverse rest' qF pad hqf]
              simp only [encodeUniversal, List.append_assoc]

end APSCounting893.Main
end Component_52

section Component_53

set_option autoImplicit false
namespace APSCounting893.Main

lemma length_le_flatMap_of_mem {α : Type} (f : α → Word) (xs : List α) (a : α) (ha : a ∈ xs) :
    (f a).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
      simp only [List.flatMap_cons, List.length_append]
      rcases List.mem_cons.mp ha with h | h
      · subst a; omega
      · have hh := ih h; omega

lemma bits_length_le_encodeNat_length (n : ℕ) : n.bits.length ≤ (encodeNat n).length := by
  simp only [encodeNat, List.length_append, List.length_replicate, List.length_singleton]
  omega

lemma field_bits_length_le_encodeExponent {k : ℕ} (a : Fin (k + 1) →₀ ℕ) (i : Fin (k + 1)) :
    (a i).bits.length ≤ (encodeExponent a).length := by
  have h := length_le_flatMap_of_mem encodeNat (List.ofFn (fun j => a j)) (a i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hb := bits_length_le_encodeNat_length (a i)
  simp only [encodeExponent, encodeList, List.length_append]
  omega

lemma decodeExistential_sizes {k : ℕ} (w : Word) (a : Fin (k + 1) →₀ ℕ) (q : ℕ)
    (h : decodeExistential k w = some (a, q)) :
    (∀ i, (a i).bits.length ≤ w.length) ∧ q.bits.length ≤ w.length := by
  obtain ⟨pad, rfl⟩ := decodeExistential_inverse w a q h
  simp only [encodeExistential, List.length_append]
  constructor
  · intro i; have hh := field_bits_length_le_encodeExponent a i; omega
  · have hh := bits_length_le_encodeNat_length q; omega

lemma decodeUniversal_sizes {k : ℕ} (w : Word) (e : Fin (k + 1) →₀ ℕ) (qE qF : ℕ)
    (h : decodeUniversal k w = some (e, qE, qF)) :
    (∀ i, (e i).bits.length ≤ w.length) ∧ qE.bits.length ≤ w.length ∧ qF.bits.length ≤ w.length := by
  obtain ⟨pad, rfl⟩ := decodeUniversal_inverse w e qE qF h
  simp only [encodeUniversal, List.length_append]
  refine ⟨?_, ?_, ?_⟩
  · intro i; have hh := field_bits_length_le_encodeExponent e i; omega
  · have hh := bits_length_le_encodeNat_length qE; omega
  · have hh := bits_length_le_encodeNat_length qF; omega

lemma decodePair_sizes (w x y : Word) (h : decodePair w = some (x, y)) :
    x.length ≤ w.length ∧ y.length ≤ w.length := by
  rw [decodePair_inverse w x y h, pairWord_length]
  omega

end APSCounting893.Main
end Component_53

section Component_54

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma trailing_parse_universal_prefix {k : ℕ} (A : Language) (cfg : TrailingConfig k)
    (hs : cfg.state = .at .uPrefix .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs ((0 : Fin (Fintype.card (TrailingReg k) + 2))) = w)
    (hc : cfg.regs (trailingRegIndex .natCount) = [])
    (hempty : ∀ i : Fin (k + 1), cfg.regs (trailingRegIndex (.eField i)) = [])
    (hqempty : cfg.regs (trailingRegIndex .qE) = [])
    (a : Fin (k + 1) →₀ ℕ) (q : ℕ) (pad : Word)
    (hword : w = encodeExponent a ++ (encodeNat q ++ pad)) :
    ∃ t ≤ (encodeNat (k + 1)).length + 2 + (k + 2) * (5 * w.length + 3), ∃ out,
      (trailingBaseProgram k).exec A cfg t = out ∧ out.state = .at .finalBit .entry ∧ out.answer = none ∧ out.regs 0 = pad ∧
      (∀ i, out.regs (trailingRegIndex (.eField i)) = (a i).bits.reverse) ∧
      out.regs (trailingRegIndex .qE) = q.bits.reverse ∧ out.regs (trailingRegIndex .natCount) = [] ∧
      (∀ j, j ≠ (0 : Fin (Fintype.card (TrailingReg k) + 2)) → j ≠ trailingRegIndex .qE →
        (∀ i : Fin (k + 1), j ≠ trailingRegIndex (.eField i)) → out.regs j = cfg.regs j) := by
  classical
  have hinput : cfg.regs (trailingParseSource false) = encodeExponent a ++ (encodeNat q ++ pad) := hw.trans hword
  have hB : (∀ i, (a i).bits.length ≤ w.length) ∧ q.bits.length ≤ w.length := by
    constructor
    · intro i
      have hh := field_bits_length_le_encodeExponent a i
      rw [hword, List.length_append, List.length_append]
      omega
    · have hh := bits_length_le_encodeNat_length q
      rw [hword, List.length_append, List.length_append]
      omega
  obtain ⟨t, ht, C, hex, hst, hans, hsrc, hcounter, hdata, hframe⟩ :=
    trailing_parse_exponent A false cfg hs ha a (encodeNat q ++ pad) w.length hinput hc hempty hB.1
  have hqC : C.regs (trailingBitReg .earlier) = [] := by
    change C.regs (trailingRegIndex .qE) = []
    rw [hframe (trailingRegIndex .qE) (by simp [trailingParseSource, Ne.symm (trailingRegIndex_ne_zero _)])
      (by intro i; simp [trailingParseReg]), hqempty]
  have hstep := trailing_parse_bit A .earlier C hst hans q pad hsrc hcounter hqC
  let out : TrailingConfig k :=
    { state := .at .finalBit .entry,
      regs := Function.update (Function.update C.regs ((0 : Fin (Fintype.card (TrailingReg k) + 2))) pad)
        (trailingRegIndex .qE) q.bits.reverse, answer := none }
  have hstep' : (trailingBaseProgram k).exec A C (5 * q.bits.length + 3) = out := hstep
  refine ⟨t + (5 * q.bits.length + 3), ?_, out, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have hqb := hB.2
    nlinarith
  · rw [StackProgram.exec_add, hex, hstep']
  · simp [out, Ne.symm (trailingRegIndex_ne_zero _)]
  · intro i
    simpa [out, trailingParseReg] using hdata i
  · simp [out]
  · simpa [out] using hcounter
  · intro j hji hjq hjfield
    simp only [out, Function.update_of_ne hjq, Function.update_of_ne hji]
    exact hframe j hji (by simpa only [trailingParseReg, Bool.false_eq_true, if_false] using hjfield)

end APSCounting893.Main
end Component_54

section Component_55

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma trailing_parse_universal {k : ℕ} (A : Language) (cfg : TrailingConfig k)
    (hs : cfg.state = .at .uPrefix .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs 0 = w) (hc : cfg.regs (trailingRegIndex .natCount) = [])
    (hempty : ∀ i : Fin (k + 1), cfg.regs (trailingRegIndex (.eField i)) = [])
    (hqEempty : cfg.regs (trailingRegIndex .qE) = []) (hqFempty : cfg.regs (trailingRegIndex .qF) = [])
    (e : Fin (k + 1) →₀ ℕ) (qE qF : ℕ) (hdecode : decodeUniversal k w = some (e, qE, qF)) :
    ∃ t ≤ (encodeNat (k + 1)).length + 2 + (k + 3) * (5 * w.length + 3), ∃ out,
      (trailingBaseProgram k).exec A cfg t = out ∧ out.state = .at (.build .earlier .bitFirst) .entry ∧ out.answer = none ∧
      (∀ i, out.regs (trailingRegIndex (.eField i)) = (e i).bits.reverse) ∧
      out.regs (trailingRegIndex .qE) = qE.bits.reverse ∧ out.regs (trailingRegIndex .qF) = qF.bits.reverse ∧
      out.regs (trailingRegIndex .natCount) = [] ∧
      (∀ j, j ≠ 0 → j ≠ trailingRegIndex .qE → j ≠ trailingRegIndex .qF →
        (∀ i : Fin (k + 1), j ≠ trailingRegIndex (.eField i)) → out.regs j = cfg.regs j) := by
  classical
  obtain ⟨pad, hword⟩ := decodeUniversal_inverse w e qE qF hdecode
  have hword' : w = encodeExponent e ++ (encodeNat qE ++ (encodeNat qF ++ pad)) := by
    simpa only [encodeUniversal, List.append_assoc] using hword
  obtain ⟨t, ht, C, hex, hst, hans, hsrc, hdata, hqE, hcounter, hframe⟩ :=
    trailing_parse_universal_prefix A cfg hs ha w hw hc hempty hqEempty e qE (encodeNat qF ++ pad) hword'
  have hqC : C.regs (trailingBitReg .final) = [] := by
    change C.regs (trailingRegIndex .qF) = []
    rw [hframe (trailingRegIndex .qF) (trailingRegIndex_ne_zero _) (by simp) (by intro i; simp), hqFempty]
  have hstep := trailing_parse_bit A .final C hst hans qF pad hsrc hcounter hqC
  let out : TrailingConfig k :=
    { state := .at (.build .earlier .bitFirst) .entry,
      regs := Function.update (Function.update C.regs 0 pad) (trailingRegIndex .qF) qF.bits.reverse, answer := none }
  have hstep' : (trailingBaseProgram k).exec A C (5 * qF.bits.length + 3) = out := hstep
  refine ⟨t + (5 * qF.bits.length + 3), ?_, out, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have hB := (decodeUniversal_sizes w e qE qF hdecode).2.2
    nlinarith
  · rw [StackProgram.exec_add, hex, hstep']
  · intro i; simpa [out] using hdata i
  · simpa [out] using hqE
  · simp [out]
  · simpa [out] using hcounter
  · intro j hj0 hjqe hjqf hjfield
    simp only [out, Function.update_of_ne hjqf, Function.update_of_ne hj0]
    exact hframe j hj0 hjqe hjfield

end APSCounting893.Main
end Component_55

section Component_56

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma trailing_parse_universal_failure {k : ℕ} (A : Language) (cfg : TrailingConfig k)
    (hs : cfg.state = .at .uPrefix .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs ((0 : Fin (Fintype.card (TrailingReg k) + 2))) = w)
    (hc : cfg.regs (trailingRegIndex .natCount) = [])
    (hempty : ∀ i : Fin (k + 1), cfg.regs (trailingRegIndex (.eField i)) = [])
    (hqempty : cfg.regs (trailingRegIndex .qE) = [])
    (hqFempty : cfg.regs (trailingRegIndex .qF) = [])
    (hdecode : decodeUniversal k w = none) :
    ∃ t ≤ (encodeNat (k + 1)).length + 2 + (k + 3) * (5 * w.length + 3),
      ((trailingBaseProgram k).exec A cfg t).answer = none ∧
      ((trailingBaseProgram k).exec A cfg t).state = .halt true := by
  classical
  cases he : decodeExponent k w with
  | none =>
      obtain ⟨t, ht, hans, hst⟩ := trailing_parse_exponent_failure A false cfg hs ha w hw hc hempty he
      exact ⟨t, by nlinarith, hans, hst⟩
  | some pair =>
      rcases pair with ⟨a, rest⟩
      have hword := decodeExponent_inverse k w a rest he
      cases hqe : decodeNat rest with
      | none =>
          have hrest : rest.length ≤ w.length := by rw [hword, List.length_append]; omega
          have hB (i : Fin (k + 1)) : (a i).bits.length ≤ w.length := by
            have hh := field_bits_length_le_encodeExponent a i
            rw [hword, List.length_append]
            omega
          obtain ⟨t, ht, C, hex, hst, hans, hsrc, hcounter, hdata, hframe⟩ :=
            trailing_parse_exponent A false cfg hs ha a rest w.length (hw.trans hword) hc hempty hB
          have hqC : C.regs (trailingBitReg .earlier) = [] := by
            change C.regs (trailingRegIndex .qE) = []
            rw [hframe (trailingRegIndex .qE) (by simp [trailingParseSource])
              (by intro i; simp [trailingParseReg]), hqempty]
          obtain ⟨s, hsB, han2, hst2⟩ := trailing_parse_bit_failure A .earlier C hst hans rest hsrc hcounter hqC hqe
          refine ⟨t + s, by nlinarith, ?_⟩
          rw [StackProgram.exec_add, hex]
          exact ⟨han2, hst2⟩
      | some pair =>
          rcases pair with ⟨qE, rest'⟩
          have hqf : decodeNat rest' = none := by
            cases hqf : decodeNat rest' with
            | none => rfl
            | some pair => simp [decodeUniversal, he, hqe, hqf] at hdecode
          have hinput : w = encodeExponent a ++ (encodeNat qE ++ rest') := by
            rw [hword, decodeNat_inverse rest qE rest' hqe]
          obtain ⟨t, ht, C, hex, hst, hans, hsrc, hdata, hqE, hcounter, hframe⟩ :=
            trailing_parse_universal_prefix A cfg hs ha w hw hc hempty hqempty a qE rest' hinput
          have hqC : C.regs (trailingBitReg .final) = [] := by
            change C.regs (trailingRegIndex .qF) = []
            rw [hframe (trailingRegIndex .qF) (trailingRegIndex_ne_zero _) (by simp) (by intro i; simp), hqFempty]
          obtain ⟨s, hsB, hans2, hst2⟩ := trailing_parse_bit_failure A .final C hst hans rest' hsrc hcounter hqC hqf
          have hrest : rest'.length ≤ w.length := by rw [hinput, List.length_append, List.length_append]; omega
          refine ⟨t + s, by nlinarith, ?_⟩
          rw [StackProgram.exec_add, hex]
          exact ⟨hans2, hst2⟩

end APSCounting893.Main
end Component_56

section Component_57

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def TrailingUniversalSafe {k : ℕ} (j : Fin (Fintype.card (TrailingReg k) + 2)) : Prop :=
  j ≠ 0 ∧ j ≠ trailingRegIndex .qE ∧ j ≠ trailingRegIndex .qF ∧
    ∀ i : Fin (k + 1), j ≠ trailingRegIndex (.eField i)

lemma trailing_universal_stage {k : ℕ} (A : Language) (cfg : TrailingConfig k)
    (hs : cfg.state = .at .uPrefix .entry) (ha : cfg.answer = none) (hc : TrailingClean cfg)
    (x u : Word) (a : Fin (k + 1) →₀ ℕ) (N : ℕ) (hx : x.length ≤ N) (hu : u.length ≤ N)
    (hw : cfg.regs 0 = u) (hcounter : cfg.regs (trailingRegIndex .natCount) = [])
    (hEmpty : ∀ i : Fin (k + 1), cfg.regs (trailingRegIndex (.eField i)) = [])
    (hqe : cfg.regs (trailingRegIndex .qE) = []) (hqf : cfg.regs (trailingRegIndex .qF) = [])
    (hfieldsA : ∀ i, cfg.regs (trailingRegIndex (.aField i)) = (a i).bits.reverse)
    (hBA : ∀ i, (a i).bits.length ≤ N)
    (hp : cfg.regs (trailingRegIndex .inputPrefix) = encodeNat x.length ++ x)
    (hEempty : cfg.regs (trailingRegIndex .queryE) = []) (hFempty : cfg.regs (trailingRegIndex .queryF) = [])
    (hl : cfg.regs (trailingRegIndex .leftClone) = []) (hr : cfg.regs (trailingRegIndex .rightClone) = []) :
    ∃ t ≤ 600 * (k + 3) * (N + 1), ∃ b : Bool,
      ((trailingBaseProgram k).exec A cfg t).answer = some b ∧
      (b = true ↔ match decodeUniversal k u with
        | none => True
        | some (e, qE, qF) =>
            (¬ List.Lex (· < ·) (trailingSuffix e 0) (trailingSuffix a 0) ∨
              ¬ A (coefficientQuery x e .numerator qE)) ∧
              ¬ A (coefficientQuery x (orderExponent (List.ofFn (fun i : Fin k => i.castSucc)) a) .numerator qF)) := by
  classical
  have hconst : (encodeNat (k + 1)).length ≤ 3 * (k + 1) + 1 := by
    have hb := bits_length_le_self (k + 1)
    simp only [encodeNat, List.length_append, List.length_replicate, List.length_singleton]
    omega
  cases hdecode : decodeUniversal k u with
  | none =>
      obtain ⟨t, ht, han, hst⟩ := trailing_parse_universal_failure A cfg hs ha u hw hcounter hEmpty hqe hqf hdecode
      have hh := assemble_failure_halts (trailingTable k) .outerPair A
        ((trailingBaseProgram k).exec A cfg t) true hst han
      refine ⟨t + 1, by nlinarith, true, ?_, by simp [hdecode]⟩
      rw [StackProgram.exec_succ]
      exact hh
  | some tuple =>
      rcases tuple with ⟨e, qE, qF⟩
      obtain ⟨t, ht, C, hex, hst, han, hdata, hqE, hqF, hcount, hframe⟩ :=
        trailing_parse_universal A cfg hs ha u hw hcounter hEmpty hqe hqf e qE qF hdecode
      have hf (j) (hj : TrailingUniversalSafe (k := k) j) : C.regs j = cfg.regs j :=
        hframe j hj.1 hj.2.1 hj.2.2.1 hj.2.2.2
      have hcC : TrailingClean C := by
        constructor
        · rw [hf (trailingRegIndex .first) (by simp [TrailingUniversalSafe])]; exact hc.first
        · rw [hf (trailingRegIndex .second) (by simp [TrailingUniversalSafe])]; exact hc.second
        · rw [hf (trailingRegIndex .copyTmp) (by simp [TrailingUniversalSafe])]; exact hc.tmp
        · rw [hf (trailingRegIndex .copyScratch) (by simp [TrailingUniversalSafe])]; exact hc.scratch
      have hA : ∀ i, C.regs (trailingRegIndex (.aField i)) = (a i).bits.reverse := by
        intro i
        rw [hf (trailingRegIndex (.aField i)) (by simp [TrailingUniversalSafe]), hfieldsA i]
      have hpC : C.regs (trailingRegIndex .inputPrefix) = encodeNat x.length ++ x := by
        rw [hf (trailingRegIndex .inputPrefix) (by simp [TrailingUniversalSafe]), hp]
      have hEC : C.regs (trailingRegIndex .queryE) = [] := by
        rw [hf (trailingRegIndex .queryE) (by simp [TrailingUniversalSafe]), hEempty]
      have hFC : C.regs (trailingRegIndex .queryF) = [] := by
        rw [hf (trailingRegIndex .queryF) (by simp [TrailingUniversalSafe]), hFempty]
      have hlC : C.regs (trailingRegIndex .leftClone) = [] := by
        rw [hf (trailingRegIndex .leftClone) (by simp [TrailingUniversalSafe]), hl]
      have hrC : C.regs (trailingRegIndex .rightClone) = [] := by
        rw [hf (trailingRegIndex .rightClone) (by simp [TrailingUniversalSafe]), hr]
      have hsize := decodeUniversal_sizes u e qE qF hdecode
      obtain ⟨s, hsB, b, hb, hiff⟩ := trailing_post_universal A C hst han hcC x e a qE qF N hx
        (hsize.2.1.trans hu) (hsize.2.2.trans hu) hqE hqF hdata hA (fun i => (hsize.1 i).trans hu)
        hBA hpC hEC hFC hlC hrC
      refine ⟨t + s, by nlinarith, b, ?_, ?_⟩
      · rw [StackProgram.exec_add, hex]
        exact hb
      · simpa only [hdecode] using hiff

end APSCounting893.Main
end Component_57

section Component_58

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def TrailingCandidateSafe {k : ℕ} (j : Fin (Fintype.card (TrailingReg k) + 2)) : Prop :=
  j ≠ trailingRegIndex .lengthMSB ∧ j ≠ trailingRegIndex .inputPrefix ∧ j ≠ trailingRegIndex .queryA

lemma trailing_candidate_stage {k : ℕ} (A : Language) (cfg : TrailingConfig k)
    (hs : cfg.state = .at .copyXForLength .entry) (ha : cfg.answer = none) (hc : TrailingClean cfg)
    (x u : Word) (a : Fin (k + 1) →₀ ℕ) (q N : ℕ)
    (hx : x.length ≤ N) (hu : u.length ≤ N) (hqa : q.bits.length ≤ N)
    (hX : cfg.regs (trailingRegIndex .x) = x) (hU : cfg.regs 0 = u)
    (hbit : cfg.regs (trailingRegIndex .qA) = q.bits.reverse)
    (hfieldsA : ∀ i, cfg.regs (trailingRegIndex (.aField i)) = (a i).bits.reverse)
    (hBA : ∀ i, (a i).bits.length ≤ N)
    (hEmpty : ∀ i : Fin (k + 1), cfg.regs (trailingRegIndex (.eField i)) = [])
    (hcounter : cfg.regs (trailingRegIndex .natCount) = [])
    (hlength : cfg.regs (trailingRegIndex .lengthLSB) = []) (hmsb : cfg.regs (trailingRegIndex .lengthMSB) = [])
    (hprefix : cfg.regs (trailingRegIndex .inputPrefix) = [])
    (hAempty : cfg.regs (trailingRegIndex .queryA) = [])
    (hEempty : cfg.regs (trailingRegIndex .queryE) = []) (hFempty : cfg.regs (trailingRegIndex .queryF) = [])
    (hqe : cfg.regs (trailingRegIndex .qE) = []) (hqf : cfg.regs (trailingRegIndex .qF) = [])
    (hl : cfg.regs (trailingRegIndex .leftClone) = []) (hr : cfg.regs (trailingRegIndex .rightClone) = []) :
    ∃ t ≤ 1000 * (k + 3) * (N + 1) ^ 2, ∃ b : Bool,
      ((trailingBaseProgram k).exec A cfg t).answer = some b ∧
      (b = true ↔ A (coefficientQuery x a .numerator q) ∧
        match decodeUniversal k u with
        | none => True
        | some (e, qE, qF) =>
            (¬ List.Lex (· < ·) (trailingSuffix e 0) (trailingSuffix a 0) ∨
              ¬ A (coefficientQuery x e .numerator qE)) ∧
              ¬ A (coefficientQuery x (orderExponent (List.ofFn (fun i : Fin k => i.castSucc)) a) .numerator qF)) := by
  classical
  let ptime := ((7 * x.length + 3) + lengthCountTime 0 x.length + (2 * x.length.bits.length + 1) +
    (7 * x.length + 3) + (18 * x.length.bits.length + 9))
  let C0 : TrailingConfig k :=
    { state := .at (.build .candidate .bitFirst) .entry,
      regs := Function.update (Function.update cfg.regs (trailingRegIndex .lengthMSB) x.length.bits.reverse)
        (trailingRegIndex .inputPrefix) (encodeNat x.length ++ x), answer := none }
  have hpRun : (trailingBaseProgram k).exec A cfg ptime = C0 :=
    trailing_input_prefix A cfg hs ha hc x hX hlength hmsb hprefix
  have hpTime : ptime ≤ 100 * (N + 1) ^ 2 := by
    have hh := trailing_input_prefix_time_bound x.length
    have hm := Nat.pow_le_pow_left (show x.length + 1 ≤ N + 1 by omega) 2
    exact hh.trans (Nat.mul_le_mul_left 100 hm)
  have hc0 : TrailingClean C0 := by
    constructor
    · simpa [C0] using hc.first
    · simpa [C0] using hc.second
    · simpa [C0] using hc.tmp
    · simpa [C0] using hc.scratch
  obtain ⟨t, ht, hex⟩ := trailing_build_query A .candidate C0 rfl rfl hc0 x a q N
    (by simpa [C0, trailingBitReg] using hbit)
    (by intro i; right; simpa [C0, trailingFieldReg] using hfieldsA i)
    (by intro h; cases h) hBA (by simp [C0]) (by simpa [C0, trailingQueryReg] using hAempty)
  have hbuildTime : t ≤ 100 * (k + 2) * (N + 1) := by
    apply ht.trans
    have hh := trailing_build_query_time_bound k N x.length q.bits.length N hx hqa le_rfl
    simpa only [List.length_append, Nat.mul_add, Nat.add_assoc] using hh
  let C1 : TrailingConfig k :=
    { state := .at .askA .entry,
      regs := Function.update C0.regs (trailingRegIndex .queryA) (coefficientQuery x a .numerator q), answer := none }
  have hex' : (trailingBaseProgram k).exec A C0 t = C1 := hex
  let C2 : TrailingConfig k :=
    { state := if A (coefficientQuery x a .numerator q) then .at .uPrefix .entry else .at .reject .entry,
      regs := Function.update C1.regs (trailingRegIndex .queryA) [], answer := none }
  have hquery : (trailingBaseProgram k).step A C1 = C2 := by
    have hh := assemble_query (trailingTable k) .outerPair .askA .uPrefix .reject A
      (trailingRegIndex .queryA) (by rfl) C1 rfl rfl
    simpa only [trailingBaseProgram, C1, Function.update_self] using hh
  have hpre : (trailingBaseProgram k).exec A cfg (ptime + t + 1) = C2 := by
    rw [StackProgram.exec_succ, StackProgram.exec_add, hpRun, hex', hquery]
  by_cases hnonzero : A (coefficientQuery x a .numerator q)
  · have hs2 : C2.state = .at .uPrefix .entry := by simp [C2, hnonzero]
    have hf (j) (hj : TrailingCandidateSafe (k := k) j) : C2.regs j = cfg.regs j := by
      simp only [C2, C1, C0, Function.update_of_ne hj.2.2, Function.update_of_ne hj.2.1,
        Function.update_of_ne hj.1]
    have hc2 : TrailingClean C2 := by
      constructor
      · rw [hf (trailingRegIndex .first) (by simp [TrailingCandidateSafe])]; exact hc.first
      · rw [hf (trailingRegIndex .second) (by simp [TrailingCandidateSafe])]; exact hc.second
      · rw [hf (trailingRegIndex .copyTmp) (by simp [TrailingCandidateSafe])]; exact hc.tmp
      · rw [hf (trailingRegIndex .copyScratch) (by simp [TrailingCandidateSafe])]; exact hc.scratch
    have hU2 : C2.regs 0 = u := by
      rw [hf 0 (by simp [TrailingCandidateSafe, Ne.symm (trailingRegIndex_ne_zero _)]), hU]
    have hA2 : ∀ i, C2.regs (trailingRegIndex (.aField i)) = (a i).bits.reverse := by
      intro i; rw [hf (trailingRegIndex (.aField i)) (by simp [TrailingCandidateSafe]), hfieldsA i]
    have hE2 : ∀ i : Fin (k + 1), C2.regs (trailingRegIndex (.eField i)) = [] := by
      intro i; rw [hf (trailingRegIndex (.eField i)) (by simp [TrailingCandidateSafe]), hEmpty i]
    have hp2 : C2.regs (trailingRegIndex .inputPrefix) = encodeNat x.length ++ x := by simp [C2, C1, C0]
    have hcounter2 : C2.regs (trailingRegIndex .natCount) = [] := by
      rw [hf (trailingRegIndex .natCount) (by simp [TrailingCandidateSafe]), hcounter]
    have hqe2 : C2.regs (trailingRegIndex .qE) = [] := by
      rw [hf (trailingRegIndex .qE) (by simp [TrailingCandidateSafe]), hqe]
    have hqf2 : C2.regs (trailingRegIndex .qF) = [] := by
      rw [hf (trailingRegIndex .qF) (by simp [TrailingCandidateSafe]), hqf]
    have hEempty2 : C2.regs (trailingRegIndex .queryE) = [] := by
      rw [hf (trailingRegIndex .queryE) (by simp [TrailingCandidateSafe]), hEempty]
    have hFempty2 : C2.regs (trailingRegIndex .queryF) = [] := by
      rw [hf (trailingRegIndex .queryF) (by simp [TrailingCandidateSafe]), hFempty]
    have hl2 : C2.regs (trailingRegIndex .leftClone) = [] := by
      rw [hf (trailingRegIndex .leftClone) (by simp [TrailingCandidateSafe]), hl]
    have hr2 : C2.regs (trailingRegIndex .rightClone) = [] := by
      rw [hf (trailingRegIndex .rightClone) (by simp [TrailingCandidateSafe]), hr]
    obtain ⟨s, hsB, b, hb, hiff⟩ := trailing_universal_stage A C2 hs2 rfl hc2 x u a N hx hu hU2
      hcounter2 hE2 hqe2 hqf2 hA2 hBA hp2 hEempty2 hFempty2 hl2 hr2
    refine ⟨ptime + t + 1 + s, ?_, b, ?_, ?_⟩
    · have hm : N + 1 ≤ (N + 1) ^ 2 := by nlinarith
      nlinarith [Nat.mul_le_mul_left (k + 3) hm]
    · rw [StackProgram.exec_add, hpre]
      exact hb
    · constructor
      · intro hb
        exact ⟨hnonzero, hiff.mp hb⟩
      · rintro ⟨_, hu⟩
        exact hiff.mpr hu
  · have hhalt : (trailingBaseProgram k).step A C2 = { C2 with answer := some false } :=
      assemble_halt (trailingTable k) .outerPair .reject A false (by rfl) C2 (by simp [C2, hnonzero]) rfl
    refine ⟨ptime + t + 1 + 1, ?_, false, ?_, by simp [hnonzero]⟩
    · have hm : N + 1 ≤ (N + 1) ^ 2 := by nlinarith
      nlinarith [Nat.mul_le_mul_left (k + 3) hm]
    · rw [StackProgram.exec_succ, hpre, hhalt]

end APSCounting893.Main
end Component_58

section Component_59

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma trailing_parse_existential {k : ℕ} (A : Language) (cfg : TrailingConfig k)
    (hs : cfg.state = .at .aPrefix .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs (trailingRegIndex .inner) = w)
    (hc : cfg.regs (trailingRegIndex .natCount) = [])
    (hempty : ∀ i : Fin (k + 1), cfg.regs (trailingRegIndex (.aField i)) = [])
    (hqempty : cfg.regs (trailingRegIndex .qA) = [])
    (a : Fin (k + 1) →₀ ℕ) (q : ℕ) (hdecode : decodeExistential k w = some (a, q)) :
    ∃ t ≤ (encodeNat (k + 1)).length + 2 + (k + 2) * (5 * w.length + 3), ∃ out,
      (trailingBaseProgram k).exec A cfg t = out ∧ out.state = .at .copyXForLength .entry ∧ out.answer = none ∧
      (∀ i, out.regs (trailingRegIndex (.aField i)) = (a i).bits.reverse) ∧
      out.regs (trailingRegIndex .qA) = q.bits.reverse ∧ out.regs (trailingRegIndex .natCount) = [] ∧
      (∀ j, j ≠ trailingRegIndex .inner → j ≠ trailingRegIndex .qA →
        (∀ i : Fin (k + 1), j ≠ trailingRegIndex (.aField i)) → out.regs j = cfg.regs j) := by
  classical
  obtain ⟨pad, hword⟩ := decodeExistential_inverse w a q hdecode
  have hinput : cfg.regs (trailingParseSource true) = encodeExponent a ++ (encodeNat q ++ pad) := by
    simpa only [trailingParseSource, Bool.true_eq, if_true, encodeExistential, List.append_assoc] using hw.trans hword
  have hB := decodeExistential_sizes w a q hdecode
  obtain ⟨t, ht, C, hex, hst, hans, hsrc, hcounter, hdata, hframe⟩ :=
    trailing_parse_exponent A true cfg hs ha a (encodeNat q ++ pad) w.length hinput hc hempty hB.1
  have hqC : C.regs (trailingBitReg .candidate) = [] := by
    change C.regs (trailingRegIndex .qA) = []
    rw [hframe (trailingRegIndex .qA) (by simp [trailingParseSource])
      (by intro i; simp [trailingParseReg]), hqempty]
  have hstep := trailing_parse_bit A .candidate C hst hans q pad hsrc hcounter hqC
  let out : TrailingConfig k :=
    { state := .at .copyXForLength .entry,
      regs := Function.update (Function.update C.regs (trailingRegIndex .inner) pad)
        (trailingRegIndex .qA) q.bits.reverse, answer := none }
  have hstep' : (trailingBaseProgram k).exec A C (5 * q.bits.length + 3) = out := hstep
  refine ⟨t + (5 * q.bits.length + 3), ?_, out, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · have hqb := hB.2
    nlinarith
  · rw [StackProgram.exec_add, hex, hstep']
  · intro i
    simpa [out, trailingParseReg] using hdata i
  · simp [out]
  · simpa [out] using hcounter
  · intro j hji hjq hjfield
    simp only [out, Function.update_of_ne hjq, Function.update_of_ne hji]
    exact hframe j hji (by simpa only [trailingParseReg, Bool.true_eq, if_true] using hjfield)

lemma trailing_parse_existential_failure {k : ℕ} (A : Language) (cfg : TrailingConfig k)
    (hs : cfg.state = .at .aPrefix .entry) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs (trailingRegIndex .inner) = w)
    (hc : cfg.regs (trailingRegIndex .natCount) = [])
    (hempty : ∀ i : Fin (k + 1), cfg.regs (trailingRegIndex (.aField i)) = [])
    (hqempty : cfg.regs (trailingRegIndex .qA) = [])
    (hdecode : decodeExistential k w = none) :
    ∃ t ≤ (encodeNat (k + 1)).length + 2 + (k + 2) * (5 * w.length + 3),
      ((trailingBaseProgram k).exec A cfg t).answer = none ∧
      ((trailingBaseProgram k).exec A cfg t).state = .halt false := by
  classical
  cases he : decodeExponent k w with
  | none =>
      obtain ⟨t, ht, hans, hst⟩ := trailing_parse_exponent_failure A true cfg hs ha w hw hc hempty he
      exact ⟨t, by nlinarith, hans, hst⟩
  | some pair =>
      rcases pair with ⟨a, rest⟩
      have hword := decodeExponent_inverse k w a rest he
      have hq : decodeNat rest = none := by
        cases hq : decodeNat rest with
        | none => rfl
        | some pair => simp [decodeExistential, he, hq] at hdecode
      have hrest : rest.length ≤ w.length := by rw [hword, List.length_append]; omega
      have hB (i : Fin (k + 1)) : (a i).bits.length ≤ w.length := by
        have hh := field_bits_length_le_encodeExponent a i
        rw [hword, List.length_append]
        omega
      obtain ⟨t, ht, C, hex, hst, hans, hsrc, hcounter, hdata, hframe⟩ :=
        trailing_parse_exponent A true cfg hs ha a rest w.length (hw.trans hword) hc hempty hB
      have hqC : C.regs (trailingBitReg .candidate) = [] := by
        change C.regs (trailingRegIndex .qA) = []
        rw [hframe (trailingRegIndex .qA) (by simp [trailingParseSource])
          (by intro i; simp [trailingParseReg]), hqempty]
      obtain ⟨s, hsB, han2, hst2⟩ := trailing_parse_bit_failure A .candidate C hst hans rest hsrc hcounter hqC hq
      refine ⟨t + s, by nlinarith, ?_⟩
      rw [StackProgram.exec_add, hex]
      exact ⟨han2, hst2⟩

end APSCounting893.Main
end Component_59

section Component_60

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def TrailingExistentialSafe {k : ℕ} (j : Fin (Fintype.card (TrailingReg k) + 2)) : Prop :=
  j ≠ trailingRegIndex .inner ∧ j ≠ trailingRegIndex .qA ∧
    ∀ i : Fin (k + 1), j ≠ trailingRegIndex (.aField i)

lemma trailing_existential_stage {k : ℕ} (A : Language) (cfg : TrailingConfig k)
    (hs : cfg.state = .at .aPrefix .entry) (ha : cfg.answer = none) (hc : TrailingClean cfg)
    (x aw u : Word) (N : ℕ) (hx : x.length ≤ N) (haw : aw.length ≤ N) (hu : u.length ≤ N)
    (hX : cfg.regs (trailingRegIndex .x) = x) (hU : cfg.regs 0 = u)
    (hW : cfg.regs (trailingRegIndex .inner) = aw)
    (hAfields : ∀ i : Fin (k + 1), cfg.regs (trailingRegIndex (.aField i)) = [])
    (hEfields : ∀ i : Fin (k + 1), cfg.regs (trailingRegIndex (.eField i)) = [])
    (hqa : cfg.regs (trailingRegIndex .qA) = [])
    (hcounter : cfg.regs (trailingRegIndex .natCount) = [])
    (hlength : cfg.regs (trailingRegIndex .lengthLSB) = []) (hmsb : cfg.regs (trailingRegIndex .lengthMSB) = [])
    (hprefix : cfg.regs (trailingRegIndex .inputPrefix) = [])
    (hAempty : cfg.regs (trailingRegIndex .queryA) = [])
    (hEempty : cfg.regs (trailingRegIndex .queryE) = []) (hFempty : cfg.regs (trailingRegIndex .queryF) = [])
    (hqe : cfg.regs (trailingRegIndex .qE) = []) (hqf : cfg.regs (trailingRegIndex .qF) = [])
    (hl : cfg.regs (trailingRegIndex .leftClone) = []) (hr : cfg.regs (trailingRegIndex .rightClone) = []) :
    ∃ t ≤ 1500 * (k + 3) * (N + 1) ^ 2, ∃ b : Bool,
      ((trailingBaseProgram k).exec A cfg t).answer = some b ∧
      (b = true ↔ match decodeExistential k aw with
        | none => False
        | some (a, q) => A (coefficientQuery x a .numerator q) ∧
            match decodeUniversal k u with
            | none => True
            | some (e, qE, qF) =>
                (¬ List.Lex (· < ·) (trailingSuffix e 0) (trailingSuffix a 0) ∨
                  ¬ A (coefficientQuery x e .numerator qE)) ∧
                  ¬ A (coefficientQuery x (orderExponent (List.ofFn (fun i : Fin k => i.castSucc)) a) .numerator qF)) := by
  classical
  have hconst : (encodeNat (k + 1)).length ≤ 3 * (k + 1) + 1 := by
    have hb := bits_length_le_self (k + 1)
    simp only [encodeNat, List.length_append, List.length_replicate, List.length_singleton]
    omega
  cases hdecode : decodeExistential k aw with
  | none =>
      obtain ⟨t, ht, han, hst⟩ := trailing_parse_existential_failure A cfg hs ha aw hW hcounter hAfields hqa hdecode
      have hh := assemble_failure_halts (trailingTable k) .outerPair A
        ((trailingBaseProgram k).exec A cfg t) false hst han
      refine ⟨t + 1, ?_, false, ?_, by simp⟩
      · have hm : N + 1 ≤ (N + 1) ^ 2 := by nlinarith
        nlinarith [Nat.mul_le_mul_left (k + 3) hm]
      · rw [StackProgram.exec_succ]
        exact hh
  | some pair =>
      rcases pair with ⟨a, q⟩
      obtain ⟨t, ht, C, hex, hst, han, hdata, hbit, hcount, hframe⟩ :=
        trailing_parse_existential A cfg hs ha aw hW hcounter hAfields hqa a q hdecode
      have hf (j) (hj : TrailingExistentialSafe (k := k) j) : C.regs j = cfg.regs j :=
        hframe j hj.1 hj.2.1 hj.2.2
      have hcC : TrailingClean C := by
        constructor
        · rw [hf (trailingRegIndex .first) (by simp [TrailingExistentialSafe])]; exact hc.first
        · rw [hf (trailingRegIndex .second) (by simp [TrailingExistentialSafe])]; exact hc.second
        · rw [hf (trailingRegIndex .copyTmp) (by simp [TrailingExistentialSafe])]; exact hc.tmp
        · rw [hf (trailingRegIndex .copyScratch) (by simp [TrailingExistentialSafe])]; exact hc.scratch
      have hXC : C.regs (trailingRegIndex .x) = x := by
        rw [hf (trailingRegIndex .x) (by simp [TrailingExistentialSafe]), hX]
      have hUC : C.regs 0 = u := by
        rw [hf 0 (by simp [TrailingExistentialSafe, Ne.symm (trailingRegIndex_ne_zero _)]), hU]
      have hEC : ∀ i : Fin (k + 1), C.regs (trailingRegIndex (.eField i)) = [] := by
        intro i; rw [hf (trailingRegIndex (.eField i)) (by simp [TrailingExistentialSafe]), hEfields i]
      have hcounterC : C.regs (trailingRegIndex .natCount) = [] := by
        rw [hf (trailingRegIndex .natCount) (by simp [TrailingExistentialSafe]), hcounter]
      have hlengthC : C.regs (trailingRegIndex .lengthLSB) = [] := by
        rw [hf (trailingRegIndex .lengthLSB) (by simp [TrailingExistentialSafe]), hlength]
      have hmsbC : C.regs (trailingRegIndex .lengthMSB) = [] := by
        rw [hf (trailingRegIndex .lengthMSB) (by simp [TrailingExistentialSafe]), hmsb]
      have hprefixC : C.regs (trailingRegIndex .inputPrefix) = [] := by
        rw [hf (trailingRegIndex .inputPrefix) (by simp [TrailingExistentialSafe]), hprefix]
      have hAemptyC : C.regs (trailingRegIndex .queryA) = [] := by
        rw [hf (trailingRegIndex .queryA) (by simp [TrailingExistentialSafe]), hAempty]
      have hEemptyC : C.regs (trailingRegIndex .queryE) = [] := by
        rw [hf (trailingRegIndex .queryE) (by simp [TrailingExistentialSafe]), hEempty]
      have hFemptyC : C.regs (trailingRegIndex .queryF) = [] := by
        rw [hf (trailingRegIndex .queryF) (by simp [TrailingExistentialSafe]), hFempty]
      have hqeC : C.regs (trailingRegIndex .qE) = [] := by
        rw [hf (trailingRegIndex .qE) (by simp [TrailingExistentialSafe]), hqe]
      have hqfC : C.regs (trailingRegIndex .qF) = [] := by
        rw [hf (trailingRegIndex .qF) (by simp [TrailingExistentialSafe]), hqf]
      have hlC : C.regs (trailingRegIndex .leftClone) = [] := by
        rw [hf (trailingRegIndex .leftClone) (by simp [TrailingExistentialSafe]), hl]
      have hrC : C.regs (trailingRegIndex .rightClone) = [] := by
        rw [hf (trailingRegIndex .rightClone) (by simp [TrailingExistentialSafe]), hr]
      have hsize := decodeExistential_sizes aw a q hdecode
      obtain ⟨s, hsB, b, hb, hiff⟩ := trailing_candidate_stage A C hst han hcC x u a q N hx hu
        (hsize.2.trans haw) hXC hUC hbit hdata (fun i => (hsize.1 i).trans haw) hEC
        hcounterC hlengthC hmsbC hprefixC hAemptyC hEemptyC hFemptyC hqeC hqfC hlC hrC
      refine ⟨t + s, ?_, b, ?_, ?_⟩
      · have hm : N + 1 ≤ (N + 1) ^ 2 := by nlinarith
        nlinarith [Nat.mul_le_mul_left (k + 3) hm]
      · rw [StackProgram.exec_add, hex]
        exact hb
      · exact hiff

end APSCounting893.Main
end Component_60

section Component_61

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma trailing_parse_pair_input {k : ℕ} (A : Language) (cfg : TrailingConfig k)
    (hs : cfg.state = .at .outerPair .entry) (ha : cfg.answer = none)
    (x aw u : Word) (hw : cfg.regs 0 = pairWord (pairWord x aw) u)
    (ho : cfg.regs (trailingRegIndex .outerRev) = [])
    (hi : cfg.regs (trailingRegIndex .inner) = [])
    (hxr : cfg.regs (trailingRegIndex .xRev) = [])
    (hx : cfg.regs (trailingRegIndex .x) = []) :
    ∃ out, (trailingBaseProgram k).exec A cfg
        ((3 * (pairWord x aw).length + 1) + (2 * (pairWord x aw).length + 1) +
          (3 * x.length + 1) + (2 * x.length + 1)) = out ∧
      out.state = .at .aPrefix .entry ∧ out.answer = none ∧ out.regs 0 = u ∧
      out.regs (trailingRegIndex .inner) = aw ∧ out.regs (trailingRegIndex .x) = x ∧
      (∀ j, j ≠ 0 → j ≠ trailingRegIndex .inner → j ≠ trailingRegIndex .x → out.regs j = cfg.regs j) := by
  classical
  let v := pairWord x aw
  let C1 : TrailingConfig k :=
    { state := .at .outerReverse .entry,
      regs := Function.update (Function.update cfg.regs 0 u) (trailingRegIndex .outerRev) v.reverse, answer := none }
  have h1 : (trailingBaseProgram k).exec A cfg (3 * v.length + 1) = C1 := by
    have hh := assemble_pair (trailingTable k) .outerPair .outerPair .outerReverse A
      0 (trailingRegIndex .outerRev) (trailingRegIndex_ne_zero _).symm false (by rfl) cfg hs ha v u hw
    simpa only [trailingBaseProgram, ho, List.append_nil] using hh
  let C2 : TrailingConfig k :=
    { state := .at .innerPair .entry,
      regs := Function.update (Function.update C1.regs (trailingRegIndex .outerRev) [])
        (trailingRegIndex .inner) v, answer := none }
  have h2 : (trailingBaseProgram k).exec A C1 (2 * v.length + 1) = C2 := by
    have hh := assemble_reverse (trailingTable k) .outerPair .outerReverse .innerPair A
      (trailingRegIndex .outerRev) (trailingRegIndex .inner) (by simp) (by rfl)
      C1 rfl rfl v.reverse (by simp [C1])
    simpa only [trailingBaseProgram, C1, List.length_reverse, List.reverse_reverse,
      Function.update_of_ne (by simp : trailingRegIndex (k := k) .inner ≠ trailingRegIndex .outerRev),
      Function.update_of_ne (trailingRegIndex_ne_zero (TrailingReg.inner : TrailingReg k)), hi, List.append_nil] using hh
  let C3 : TrailingConfig k :=
    { state := .at .xReverse .entry,
      regs := Function.update (Function.update C2.regs (trailingRegIndex .inner) aw)
        (trailingRegIndex .xRev) x.reverse, answer := none }
  have h3 : (trailingBaseProgram k).exec A C2 (3 * x.length + 1) = C3 := by
    have hh := assemble_pair (trailingTable k) .outerPair .innerPair .xReverse A
      (trailingRegIndex .inner) (trailingRegIndex .xRev) (by simp) false (by rfl)
      C2 rfl rfl x aw (by simp [C2, v])
    have hdst : C2.regs (trailingRegIndex .xRev) = [] := by simpa [C2, C1] using hxr
    simpa only [trailingBaseProgram, hdst, List.append_nil] using hh
  let C4 : TrailingConfig k :=
    { state := .at .aPrefix .entry,
      regs := Function.update (Function.update C3.regs (trailingRegIndex .xRev) [])
        (trailingRegIndex .x) x, answer := none }
  have h4 : (trailingBaseProgram k).exec A C3 (2 * x.length + 1) = C4 := by
    have hh := assemble_reverse (trailingTable k) .outerPair .xReverse .aPrefix A
      (trailingRegIndex .xRev) (trailingRegIndex .x) (by simp) (by rfl)
      C3 rfl rfl x.reverse (by simp [C3])
    have hdst : C3.regs (trailingRegIndex .x) = [] := by simpa [C3, C2, C1] using hx
    simpa only [trailingBaseProgram, List.length_reverse, List.reverse_reverse, hdst, List.append_nil] using hh
  have h12 : (trailingBaseProgram k).exec A cfg ((3 * v.length + 1) + (2 * v.length + 1)) = C2 := by
    rw [StackProgram.exec_add, h1, h2]
  have h123 : (trailingBaseProgram k).exec A cfg ((3 * v.length + 1) + (2 * v.length + 1) + (3 * x.length + 1)) = C3 := by
    rw [StackProgram.exec_add, h12, h3]
  refine ⟨C4, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [StackProgram.exec_add, h123, h4]
  · simp [C4, C3, C2, C1, Ne.symm (trailingRegIndex_ne_zero _)]
  · simp [C4, C3, C2, C1]
  · simp [C4]
  · intro j hj0 hji hjx
    by_cases hjo : j = trailingRegIndex .outerRev
    · subst j
      simp [C4, C3, C2, C1, ho]
    · by_cases hjxr : j = trailingRegIndex .xRev
      · subst j
        simp [C4, C3, C2, C1, hxr]
      · simp only [C4, C3, C2, C1, Function.update_of_ne hjx, Function.update_of_ne hjxr,
          Function.update_of_ne hji, Function.update_of_ne hjo, Function.update_of_ne hj0]

end APSCounting893.Main
end Component_61

section Component_62

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma trailing_parse_outer_pair {k : ℕ} (A : Language) (cfg : TrailingConfig k)
    (hs : cfg.state = .at .outerPair .entry) (ha : cfg.answer = none)
    (v u : Word) (hw : cfg.regs 0 = pairWord v u)
    (ho : cfg.regs (trailingRegIndex .outerRev) = [])
    (hi : cfg.regs (trailingRegIndex .inner) = []) :
    ∃ out, (trailingBaseProgram k).exec A cfg
        ((3 * v.length + 1) + (2 * v.length + 1)) = out ∧
      out.state = .at .innerPair .entry ∧ out.answer = none ∧ out.regs 0 = u ∧
      out.regs (trailingRegIndex .inner) = v := by
  classical
  let C1 : TrailingConfig k :=
    { state := .at .outerReverse .entry,
      regs := Function.update (Function.update cfg.regs 0 u) (trailingRegIndex .outerRev) v.reverse, answer := none }
  have h1 : (trailingBaseProgram k).exec A cfg (3 * v.length + 1) = C1 := by
    have hh := assemble_pair (trailingTable k) .outerPair .outerPair .outerReverse A
      0 (trailingRegIndex .outerRev) (trailingRegIndex_ne_zero _).symm false (by rfl) cfg hs ha v u hw
    simpa only [trailingBaseProgram, ho, List.append_nil] using hh
  let C2 : TrailingConfig k :=
    { state := .at .innerPair .entry,
      regs := Function.update (Function.update C1.regs (trailingRegIndex .outerRev) [])
        (trailingRegIndex .inner) v, answer := none }
  have h2 : (trailingBaseProgram k).exec A C1 (2 * v.length + 1) = C2 := by
    have hh := assemble_reverse (trailingTable k) .outerPair .outerReverse .innerPair A
      (trailingRegIndex .outerRev) (trailingRegIndex .inner) (by simp) (by rfl)
      C1 rfl rfl v.reverse (by simp [C1])
    simpa only [trailingBaseProgram, C1, List.length_reverse, List.reverse_reverse,
      Function.update_of_ne (by simp : trailingRegIndex (k := k) .inner ≠ trailingRegIndex .outerRev),
      Function.update_of_ne (trailingRegIndex_ne_zero (TrailingReg.inner : TrailingReg k)), hi, List.append_nil] using hh
  refine ⟨C2, ?_, rfl, rfl, ?_, ?_⟩
  · rw [StackProgram.exec_add, h1, h2]
  · simp [C2, C1, Ne.symm (trailingRegIndex_ne_zero _)]
  · simp [C2]

end APSCounting893.Main
end Component_62

section Component_63
set_option autoImplicit false
namespace APSCounting893.Main
lemma StackProgram.inOracleP
    {Q : Type} [Fintype Q] {r : ℕ} (P : APSCounting893.Main.StackProgram Q r)
    (A L : APSCounting893.Main.Language) (c d : ℕ)
    (h : ∀ x : APSCounting893.Main.Word, ∃ answer : Bool,
      (P.run A x [] (APSCounting893.Main.polyBound c d x.length)).answer = some answer ∧
        (answer = true ↔ L x)) : APSCounting893.Main.InOracleP A L := by
  exact stack_program_polynomial_simulation P A L c d h
end APSCounting893.Main
end Component_63

section Component_64

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma trailing_base_runs {k : ℕ} (rho : CoefficientRepresentation k) (w : Word) :
    ∃ t ≤ 2000 * (k + 3) * (w.length + 1) ^ 2, ∃ b : Bool,
      ((trailingBaseProgram k).run (CoefficientBitLanguage rho) w [] t).answer = some b ∧
        (b = true ↔ BaseTrailingLanguage rho w) := by
  classical
  let P := trailingBaseProgram k
  let A := CoefficientBitLanguage rho
  let cfg := P.initialConfig w []
  have hempty (reg : TrailingReg k) : cfg.regs (trailingRegIndex reg) = [] := by
    simp [cfg, StackProgram.initialConfig]
  have hinput : cfg.regs 0 = w := by simp [cfg, StackProgram.initialConfig]
  have hclock : w.length + 1 ≤ (w.length + 1) ^ 2 := by nlinarith
  cases houter : decodePair w with
  | none =>
      obtain ⟨t, ht, han, hst⟩ := assemble_pair_failure (trailingTable k) .outerPair .outerPair .outerReverse A
        0 (trailingRegIndex .outerRev) (trailingRegIndex_ne_zero _).symm false (by rfl)
        cfg rfl rfl w hinput houter
      have hh := assemble_failure_halts (trailingTable k) .outerPair A (P.exec A cfg t) false hst han
      refine ⟨t + 1, ?_, false, ?_, ?_⟩
      · nlinarith [Nat.mul_le_mul_left (k + 3) hclock]
      · change (P.exec A cfg (t + 1)).answer = some false
        rw [StackProgram.exec_succ]
        exact hh
      · simp [BaseTrailingLanguage, houter]
  | some pair =>
      rcases pair with ⟨v, u⟩
      have hword := decodePair_inverse w v u houter
      have hvsize := (decodePair_sizes w v u houter).1
      have husize := (decodePair_sizes w v u houter).2
      cases hinner : decodePair v with
      | none =>
          obtain ⟨C, hex, hst, han, hU, hV⟩ := trailing_parse_outer_pair A cfg rfl rfl v u
            (hinput.trans hword) (hempty .outerRev) (hempty .inner)
          let t0 := (3 * v.length + 1) + (2 * v.length + 1)
          obtain ⟨t, ht, han2, hst2⟩ := assemble_pair_failure (trailingTable k) .outerPair .innerPair .xReverse A
            (trailingRegIndex .inner) (trailingRegIndex .xRev) (by simp) false (by rfl)
            C hst han v hV hinner
          have hh := assemble_failure_halts (trailingTable k) .outerPair A (P.exec A C t) false hst2 han2
          refine ⟨t0 + t + 1, ?_, false, ?_, ?_⟩
          · dsimp only [t0]
            nlinarith [Nat.mul_le_mul_left (k + 3) hclock]
          · change (P.exec A cfg (t0 + t + 1)).answer = some false
            rw [StackProgram.exec_succ, StackProgram.exec_add, hex]
            exact hh
          · simp [BaseTrailingLanguage, houter, hinner]
      | some pair =>
          rcases pair with ⟨x, aw⟩
          have hvword := decodePair_inverse v x aw hinner
          have hxsize := (decodePair_sizes v x aw hinner).1.trans hvsize
          have hawsize := (decodePair_sizes v x aw hinner).2.trans hvsize
          obtain ⟨C, hex, hst, han, hU, hW, hX, hframe⟩ := trailing_parse_pair_input A cfg rfl rfl x aw u
            (by rw [← hvword]; exact hinput.trans hword)
            (hempty .outerRev) (hempty .inner) (hempty .xRev) (hempty .x)
          let t0 := ((3 * (pairWord x aw).length + 1) + (2 * (pairWord x aw).length + 1) +
            (3 * x.length + 1) + (2 * x.length + 1))
          have ht0 : t0 ≤ 10 * w.length + 4 := by
            dsimp only [t0]
            rw [← hvword]
            omega
          have hemptyC (reg : TrailingReg k) (hri : reg ≠ .inner) (hrx : reg ≠ .x) :
              C.regs (trailingRegIndex reg) = [] := by
            rw [hframe (trailingRegIndex reg) (trailingRegIndex_ne_zero _)
              (by simpa using hri) (by simpa using hrx), hempty reg]
          have hcC : TrailingClean C := by
            constructor
            · exact hemptyC .first (by simp) (by simp)
            · exact hemptyC .second (by simp) (by simp)
            · exact hemptyC .copyTmp (by simp) (by simp)
            · exact hemptyC .copyScratch (by simp) (by simp)
          have hAF : ∀ i : Fin (k + 1), C.regs (trailingRegIndex (.aField i)) = [] := by
            intro i; exact hemptyC (.aField i) (by simp) (by simp)
          have hEF : ∀ i : Fin (k + 1), C.regs (trailingRegIndex (.eField i)) = [] := by
            intro i; exact hemptyC (.eField i) (by simp) (by simp)
          obtain ⟨s, hsB, b, hb, hiff⟩ := trailing_existential_stage A C hst han hcC x aw u w.length
            hxsize hawsize husize hX hU hW hAF hEF
            (hemptyC .qA (by simp) (by simp))
            (hemptyC .natCount (by simp) (by simp))
            (hemptyC .lengthLSB (by simp) (by simp))
            (hemptyC .lengthMSB (by simp) (by simp))
            (hemptyC .inputPrefix (by simp) (by simp))
            (hemptyC .queryA (by simp) (by simp))
            (hemptyC .queryE (by simp) (by simp))
            (hemptyC .queryF (by simp) (by simp))
            (hemptyC .qE (by simp) (by simp))
            (hemptyC .qF (by simp) (by simp))
            (hemptyC .leftClone (by simp) (by simp))
            (hemptyC .rightClone (by simp) (by simp))
          refine ⟨t0 + s, ?_, b, ?_, ?_⟩
          · nlinarith [Nat.mul_le_mul_left (k + 3) hclock]
          · change (P.exec A cfg (t0 + s)).answer = some b
            rw [StackProgram.exec_add, hex]
            exact hb
          · cases hda : decodeExistential k aw with
            | none => simpa only [BaseTrailingLanguage, houter, hinner, hda] using hiff
            | some pair =>
                rcases pair with ⟨a, q⟩
                cases hdu : decodeUniversal k u with
                | none => simpa only [BaseTrailingLanguage, houter, hinner, hda, hdu, A] using hiff
                | some tuple =>
                    rcases tuple with ⟨e, qE, qF⟩
                    simpa only [BaseTrailingLanguage, houter, hinner, hda, hdu, trailingSuffix,
                      List.drop_zero, List.map_ofFn, A, Function.comp_def] using hiff

end APSCounting893.Main
end Component_64

section Component_65

set_option autoImplicit false
namespace APSCounting893.Main

lemma baseTrailing_inOracleP {k : ℕ} (rho : CoefficientRepresentation k) :
    InOracleP (CoefficientBitLanguage rho) (BaseTrailingLanguage rho) := by
  classical
  apply (trailingBaseProgram k).inOracleP (CoefficientBitLanguage rho) (BaseTrailingLanguage rho) (2000 * (k + 3)) 2
  intro w
  obtain ⟨t, ht, b, hb, hiff⟩ := trailing_base_runs rho w
  refine ⟨b, ?_, hiff⟩
  let P := trailingBaseProgram k
  let A := CoefficientBitLanguage rho
  let cfg := P.initialConfig w []
  have ht' : t ≤ polyBound (2000 * (k + 3)) 2 w.length := ht
  have he : P.exec A cfg (polyBound (2000 * (k + 3)) 2 w.length) = P.exec A cfg t := by
    rw [show polyBound (2000 * (k + 3)) 2 w.length = t + (polyBound (2000 * (k + 3)) 2 w.length - t) by omega,
      StackProgram.exec_add]
    exact P.exec_halted A (P.exec A cfg t) b hb _
  change (P.exec A cfg (polyBound (2000 * (k + 3)) 2 w.length)).answer = some b
  rw [he]
  exact hb

end APSCounting893.Main
end Component_65

theorem solution (k : ℕ)
    (rho : APSCounting893.Main.CoefficientRepresentation k) :
    APSCounting893.Main.InOracleP (APSCounting893.Main.CoefficientBitLanguage rho)
      (APSCounting893.Main.BaseTrailingLanguage rho) := by
  exact APSCounting893.Main.baseTrailing_inOracleP rho
