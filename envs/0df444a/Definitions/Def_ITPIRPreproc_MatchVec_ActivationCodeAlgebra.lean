-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_ActivationCodeAlgebra
-- name    : ITPIRPreproc_MatchVec_ActivationCodeAlgebra
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:40:19.253809+00:00
-- url     : https://prove2.me/theorems/01762351-fc92-4faf-bd21-89649c9f05ea
-- title:
--   Appendix A — length and decoding lemmas for fixed-width activation codes
-- statement:
--   Proved decoding algebra for the fixed-width activation-bit codes. Equal positive-width block lists have injective flattening; the binary vector code has length $d$ and is injective; a raw key code has length $(h+1)d$ and is injective when $d>0$; `natBits w x` has length $w$; and two-bit encodings of $\mathbb F_3$ vectors have length $2d$ and are injective. These are precisely the decoding steps used by Claim 6.2.4(iv). The zero-width edge case is explicitly excluded, since flattening empty blocks cannot be injective.
-- source:
--   Claim 6.2.4(iv), printed p.23 (PDF p.25), fixed-width codes '(h+1)d bits' for keys, 'a bit' for the secret, and '2d bits' for answers; Appendix A, printed pp.38–39 (PDF pp.40–41), says codes are directly computable and code lengths are O(m log m).

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_ActivationPaddedEncoding

namespace ITPIRPreproc.MatchVec

open WordRAM
open OCHPImpl

/-- Flattening equal positive-width blocks is injective. -/
lemma flatten_inj_of_uniform_length {d : ℕ} (hd : 0 < d) {L M : List (List Bool)}
    (hL : ∀ l ∈ L, l.length = d) (hM : ∀ l ∈ M, l.length = d)
    (h : L.flatten = M.flatten) : L = M := by
  induction L generalizing M with
  | nil =>
      cases M with
      | nil => rfl
      | cons m M =>
          have hm := hM m (by simp)
          have hempty : m = [] ∧ M.flatten = [] := by
            simpa only [List.flatten_nil, List.flatten_cons, List.nil_eq,
              List.append_eq_nil_iff] using h.symm
          have hm0 : m.length = 0 := by rw [hempty.1]; rfl
          omega
  | cons l L ih =>
      cases M with
      | nil =>
          have hl := hL l (by simp)
          have hempty : l = [] ∧ L.flatten = [] := by
            simpa only [List.flatten_nil, List.flatten_cons, List.append_nil,
              List.append_eq_nil_iff] using h
          have hl0 : l.length = 0 := by rw [hempty.1]; rfl
          omega
      | cons m M =>
          simp only [List.flatten_cons] at h
          have hl := hL l (by simp)
          have hm := hM m (by simp)
          have hp := List.append_inj h (hl.trans hm.symm)
          have ht : L.flatten = M.flatten := hp.2
          have htl : L = M := ih (fun x hx => hL x (by simp [hx]))
            (fun x hx => hM x (by simp [hx])) ht
          rw [hp.1, htl]

lemma f2Bit_injective : Function.Injective (fun x : ZMod 2 => decide (x = 1)) := by decide

lemma encF2_injective : Function.Injective encF2 := by decide

@[simp] lemma encF2Vec_length {d : ℕ} (x : Fin d → ZMod 2) :
    (encF2Vec x).length = d := by simp [encF2Vec]

lemma encF2Vec_injective {d : ℕ} : Function.Injective (@encF2Vec d) := by
  intro x y h
  have hf := List.ofFn_inj.mp h
  funext k
  exact f2Bit_injective (congrFun hf k)

@[simp] lemma encActKeyRaw_length {h d : ℕ} (K : ActKey h d) :
    (encActKeyRaw K).length = (h + 1) * d := by
  simp [encActKeyRaw, List.length_flatten, List.sum_ofFn, Nat.add_mul]

lemma encActKeyRaw_injective {h d : ℕ} (hd : 0 < d) :
    Function.Injective (@encActKeyRaw h d) := by
  intro K L hEq
  unfold encActKeyRaw at hEq
  have hp := List.append_inj hEq (by simp [List.length_flatten, List.sum_ofFn])
  have hrows : (List.ofFn fun r : Fin h => List.ofFn fun k : Fin d => decide (K.1 r k = 1)) =
      (List.ofFn fun r : Fin h => List.ofFn fun k : Fin d => decide (L.1 r k = 1)) :=
    flatten_inj_of_uniform_length hd (by simp) (by simp) hp.1
  have hmat : K.1 = L.1 := by
    funext r k
    apply f2Bit_injective
    exact congrFun (List.ofFn_inj.mp (congrFun (List.ofFn_inj.mp hrows) r)) k
  apply Prod.ext hmat
  exact encF2Vec_injective hp.2

@[simp] lemma natBits_length_eq (w x : ℕ) : (natBits w x).length = w := by
  induction w generalizing x with
  | zero => rfl
  | succ w ih => simp [natBits, ih]

lemma natBits_two_inj_of_lt_four {x y : ℕ} (hx : x < 4) (hy : y < 4)
    (h : natBits 2 x = natBits 2 y) : x = y := by
  interval_cases x <;> interval_cases y <;> revert h <;> decide

@[simp] lemma encF3Vec_length {d : ℕ} (z : Fin d → ZMod 3) :
    (encF3Vec z).length = 2 * d := by
  simp [encF3Vec, List.length_flatten, List.sum_ofFn, Nat.mul_comm]

lemma encF3Vec_injective {d : ℕ} : Function.Injective (@encF3Vec d) := by
  intro x y h
  unfold encF3Vec at h
  have hrows : (List.ofFn fun k : Fin d => natBits 2 (x k).val) =
      (List.ofFn fun k : Fin d => natBits 2 (y k).val) :=
    flatten_inj_of_uniform_length (d := 2) (by omega) (by simp) (by simp) h
  funext k
  apply ZMod.val_injective 3
  apply natBits_two_inj_of_lt_four
  · have hk := ZMod.val_lt (x k); omega
  · have hk := ZMod.val_lt (y k); omega
  · exact congrFun (List.ofFn_inj.mp hrows) k

end ITPIRPreproc.MatchVec


