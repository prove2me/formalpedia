-- Prove2me | Definitions.Def_DetDLP_D4BEntryFuel
-- name    : DetDLP_D4BEntryFuel
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:30:16.802795+00:00
-- url     : https://prove2.me/theorems/2cbe1ae0-514e-4743-9aba-c907080ee412
-- title:
--   Uniform unary fuel for residual digit entry adapters
-- statement:
--   A fixed polynomial in the length of a digit query supplies enough unary fuel for its precision, output length, digit divisor, and radix. The original network vertex list bounds the boundary arity, and the plan enumerator bounds the guard.

import Definitions.Def_DetDLP_D4BSliceArgs
set_option autoImplicit false
namespace DetDLP.D4BEntry
open Groundwork Groundwork.PolyT D4Plan D4Slice AppendixD4 ResidualScalarOracle DetDLP_W1_Queries
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.flatMap PolyT.length
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86

def pad : ℕ → W → W
| 0, _ => [true]
| k+1, w => (true :: true :: w).flatMap (fun _ => pad k w)
@[local fun_prop] theorem pad_poly {α : Type} [Enc α] (k : ℕ) {w : α → W} (hw : PolyT w) : PolyT (fun a => pad k (w a)) := by
  induction k with
  | zero => exact PolyT.const _
  | succ k ih => unfold pad; apply PolyT.flatMap (f := fun a (_ : Bool) => pad k (w a)); exact ih.comp (by fun_prop); fun_prop
@[simp] theorem pad_length (k : ℕ) (w : W) : (pad k w).length = (w.length+2)^k := by
  induction k with
  | zero => simp [pad]
  | succ k ih => simp [pad,List.length_flatMap,ih,pow_succ,Nat.mul_comm]; ring
theorem flen (w : W) : (Encoding.frame w).length = 2*w.length+1 := by
  induction w with
  | nil => rfl
  | cons b w ih => change (Encoding.frame w).length+1+1=2*(w.length+1)+1; omega
theorem memberLen (w : W) (ws : List W) (h : w ∈ ws) : w.length ≤ (Encoding.encodeList id ws).length := by
  induction ws with
  | nil => simp at h
  | cons a as ih => rcases List.mem_cons.mp h with rfl|h <;> simp only [Encoding.encodeList,id_eq,List.length_cons,List.length_append,flen]; omega; have := ih h; omega

def np (k n : ℕ) := k*(n+1)^k

theorem beta_le_nV {C c : ℕ} (x : Input C c) : 4*x.m*x.k ≤ x.G.nV := by simpa [←x.spec.card_termSubdiv] using Finset.card_le_univ x.spec.termSubdivVerts

theorem infoLen {C c : ℕ} {x : Input C c} (P : Plan x) (u : Fin P.N) (a : Fin (P.R u).nV → Fin (J P u)) :
    x.desc.length ≤ (digitDesc P u a).length ∧ x.G.nV ≤ (digitDesc P u a).length := by
  have hd : (input x).length ≤ (digitDesc P u a).length := memberLen _ _ (List.mem_cons_self ..)
  constructor
  · exact (memberLen x.desc _ (List.mem_cons_self ..)).trans hd
  · have hf : (List.ofFn (fun v : Fin x.G.nV => decide (v ∈ x.spec.lookupVerts))).length ≤ (input x).length := memberLen _ _ (by simp)
    simpa only [List.length_ofFn] using hf.trans hd

theorem sizeBounds {C c : ℕ} {x : Input C c} (P : Plan x) (u : Fin P.N) (a : Fin (P.R u).nV → Fin (J P u)) :
    let L := (digitDesc P u a).length
    x.b ≤ C*L ∧ size x ≤ C*L*(C*L)+L ∧ x.b ≤ C*(size x+1)^c := by
  intro L
  obtain ⟨hd,hg⟩ := infoLen P u a
  have hβ : 4*x.m*x.k ≤ L := (beta_le_nV x).trans hg
  have hb := x.lower.trans (Nat.mul_le_mul_left C hβ)
  have hm : x.m ≤ L := by have hk := x.hk; nlinarith only [hβ, Nat.mul_le_mul_left (4*x.m) hk]
  refine ⟨hb, Nat.add_le_add (x.hS.trans (Nat.mul_le_mul (Nat.mul_le_mul_left C hm) hb)) hd, ?_⟩
  exact x.lower.trans (Nat.mul_le_mul_left C ((beta_le_nV x).trans x.nV))

theorem cap_poly (C e : ℕ) : ∃ k : ℕ, ∀ n : ℕ,
    e*(C*n)+np e (C*n*(C*n)+n)+(C*n*(C*n)+n)+2 ≤ (n+2)^k := by
  let z : ℕ → ℕ := fun n => C*n*(C*n)+n
  have hC : PB (fun _ => C) := PB.const C
  have hc := hC.mul PB.id'
  have hz : PB z := (hc.mul hc).add PB.id'
  have hw : PB (np e) := ⟨e,fun _ => le_rfl⟩
  obtain ⟨k,H⟩ := (((((PB.const e).mul hc).add (hw.comp hz)).add hz).add (PB.const 2))
  refine ⟨k+k,fun n => (H n).trans ?_⟩
  rw [pow_add]; apply Nat.mul_le_mul
  · exact (Nat.lt_two_pow_self (n:=k)).le.trans (Nat.pow_le_pow_left (by omega) _)
  · exact Nat.pow_le_pow_left (by omega) _

theorem fuelSpec {C c : ℕ} (e : ℕ) : ∃ k : ℕ, ∀ {x : Input C c} (P : Plan x) {A o}, Enumerates A o e P →
    ∀ (u : Fin P.N) (a : Fin (P.R u).nV → Fin (J P u)) (v : Fin (P.R u).nV) (t : Fin ((P.R u).deg v) → Bool),
    let len := (pad k (encodePortQuery (digitDesc P u a) v.val (List.ofFn t))).length
    spacing P.f (P.R u)*x.l ≤ len ∧ precision P.f x.l (P.R u) (h P u) (4*x.m*x.k) ≤ len ∧ h P u*(a v).val ≤ len ∧ h P u ≤ len := by
  obtain ⟨k,hk⟩ := cap_poly C e; refine ⟨k,?_⟩
  intro x P A o he u a v t len
  obtain ⟨_,_,_,_,hg,_,_,hb⟩ := he
  have hgn : P.guard ≤ np e (size x) := by unfold polyBound at hg; unfold np; exact_mod_cast hg
  obtain ⟨hu,hs,_⟩ := sizeBounds P u a
  let L := (digitDesc P u a).length
  have hq : L ≤ (encodePortQuery (digitDesc P u a) v.val (List.ofFn t)).length := memberLen _ _ (List.mem_cons_self ..)
  have H := (hk L).trans (Nat.pow_le_pow_left (Nat.add_le_add_right hq 2) k)
  change _ ≤ (_+2)^k at H
  rw [← pad_length] at H
  have hp := (hb u).1; have hl := (hb u).2
  have he' := Nat.mul_le_mul_left e hu
  have hg' : np e (size x) ≤ np e (C*L*(C*L)+L) := Nat.mul_le_mul_left e (Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) _)
  have ha : (a v).val ≤ (P.guard+x.p)/(h P u) := Nat.le_of_lt_succ (a v).isLt
  have hdiv := (Nat.mul_le_mul_left (h P u) ha).trans (Nat.mul_div_le _ _)
  have hP : x.p ≤ size x := x.pS.trans (Nat.le_add_right ..)
  have hn : 1 ≤ (P.R u).nV := by have := v.isLt; omega
  have hwidth : h P u ≤ precision P.f x.l (P.R u) (h P u) (4*x.m*x.k) := by
    unfold precision; have := Nat.mul_le_mul_right (h P u) hn; omega
  change _ ≤ len at H
  dsimp [L] at H hg'
  exact ⟨by omega,by omega,by omega,by omega⟩
end DetDLP.D4BEntry


