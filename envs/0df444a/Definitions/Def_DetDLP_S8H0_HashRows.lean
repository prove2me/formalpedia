-- Prove2me | Definitions.Def_DetDLP_S8H0_HashRows
-- name    : DetDLP_S8H0_HashRows
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:28:39.815687+00:00
-- url     : https://prove2.me/theorems/a978cbc5-42a5-4d66-88b3-880a087e25ff
-- title:
--   Wired multiplication and addition checks
-- statement:
--   Two multipliers with equality-enforced bus pins and three column adders check a multiply-add modulo the public modulus on arbitrary signal words.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_RangeRows

set_option autoImplicit false
namespace DetDLP.S8H0.HashRows
open RegisterMap NamedBlocks ResidueWires RangeRows S8J

variable {d : ℕ} {s : Shape}

abbrev Word (s : Shape) := ℕ → Ref s
def evalWord (w : Word s) (x : Bits (s.size+1)) (n : ℕ) := ∀ i, (w i).eval x = n.testBit i

def padded (f : Fin d → Ref s) (i : ℕ) : Ref s := if h : i < d then f ⟨i,h⟩ else .pin false

theorem padded_spec (f : Fin d → Ref s) (x : Bits (s.size+1)) (z : Bits d) (h : ∀ i, (f i).eval x = z i) :
    evalWord (padded f) x (value z).val := fun i => pad_eval (n:=i+1) f x z h ⟨i,by omega⟩

def pub (n : ℕ) : Word s := fun i => .pin (n.testBit i)

def sumRows (n : ℕ) (a b z : Word s) (c : Fin n → Ref s) :=
  add false (fun i : Fin n => a i.val) (fun i : Fin n => b i.val) (fun i : Fin n => z i.val) c

theorem sum_spec {n : ℕ} (hn : 0 < n) (a b z : Word s) (c : Fin n → Ref s) (x : Bits (s.size+1))
    {A B Z : ℕ} (ha : evalWord a x A) (hb : evalWord b x B) (hz : evalWord z x Z) :
    (sumRows n a b z c).OK x ↔ w3_addColumns n A B Z false (fun i => (c i).eval x) := by
  unfold evalWord at ha hb hz
  unfold sumRows; rw [add_iff]; simp only [ha,hb,hz]; exact S8C.AddLayout.columns_iff hn ..

def busRef (d : ℕ) (a b z : Word s) (i : Fin (4*d)) :=
  if i.val < d then a i.val else if i.val < 2*d then b (i.val-d) else z (i.val-2*d)

theorem bus_spec (a b z : Word s) (x : Bits (s.size+1)) {A B Z : ℕ}
    (ha : evalWord a x A) (hb : evalWord b x B) (hz : evalWord z x Z) (i : Fin (4*d)) :
    (busRef d a b z i).eval x = w3_mulBus d A B Z i := by
  unfold busRef w3_mulBus; split_ifs <;> first | apply ha | apply hb | apply hz

def product (hd : 1 ≤ d) (a b z : Word s) (w : Fin (w3_fpMulLayout d hd).nb → Ref s) :=
  joinB (mapped (w3_fpMulLayout d hd) (w3_fpMulTests d hd) w)
    (eqs (4*d) (fun i => w (w4_M5PortTensor.ext hd i)) (busRef d a b z))

theorem product_spec (hd : 1 ≤ d) (a b z : Word s) (w : Fin (w3_fpMulLayout d hd).nb → Ref s)
    (x : Bits (s.size+1)) {A B : ℕ} (Z : Fin (2^(2*d)))
    (ha : evalWord a x A) (hb : evalWord b x B) (hz : evalWord z x Z.val) :
    (product hd a b z w).OK x ↔ w3_slotMulInc hd A B (Z,fun i => (w i).eval x) := by
  unfold product; rw [joinB_iff, mapped_iff, eqs_iff]
  simp only [bus_spec a b z x ha hb hz]; exact and_comm

structure Wires (d : ℕ) (hd : 1 ≤ d) (s : Shape) where
  a : Word s
  x : Word s
  b : Word s
  z : Word s
  rem : Word s
  quot : Word s
  prod1 : Word s
  prod2 : Word s
  sum : Word s
  cp : Word s
  mul1 : Fin (w3_fpMulLayout d hd).nb → Ref s
  mul2 : Fin (w3_fpMulLayout d hd).nb → Ref s
  carry1 : Fin (2*d) → Ref s
  carry2 : Fin (d+1) → Ref s
  carry3 : Fin (d+1) → Ref s

def block {hd : 1 ≤ d} (p : ℕ) (w : Wires d hd s) :=
  joinB (joinB (product hd w.a w.x w.prod1 w.mul1) (product hd w.quot (pub p) w.prod2 w.mul2))
    (joinB (sumRows (2*d) w.prod2 w.rem w.prod1 w.carry1)
      (joinB (sumRows (d+1) w.rem w.b w.sum w.carry2) (sumRows (d+1) w.z w.cp w.sum w.carry3)))

theorem block_spec {d p : ℕ} (hd : 1 ≤ d) (w : Wires d hd s) (v : Bits (s.size+1))
    (a x b z : ℕ) (r : w3_fpHashCert d p hd) (t : w3_slotHashAux d)
    (ha : evalWord w.a v a) (hx : evalWord w.x v x) (hb : evalWord w.b v b) (hz : evalWord w.z v z)
    (hr : evalWord w.rem v r.1.1.val) (hq : evalWord w.quot v r.1.2.1.val)
    (h1 : evalWord w.prod1 v r.1.2.2.1.1.val) (h2 : evalWord w.prod2 v r.1.2.2.2.1.val)
    (hs : evalWord w.sum v t.2.1.val) (hp : evalWord w.cp v (if r.2 then p else 0))
    (hm1 : (fun i => (w.mul1 i).eval v) = r.1.2.2.1.2) (hm2 : (fun i => (w.mul2 i).eval v) = r.1.2.2.2.2)
    (hc1 : (fun i => (w.carry1 i).eval v) = t.1) (hc2 : (fun i => (w.carry2 i).eval v) = t.2.2.1)
    (hc3 : (fun i => (w.carry3 i).eval v) = t.2.2.2) :
    (block p w).OK v ↔ w3_slotHashBits hd a b x z r t := by
  let u := r.1.2.2.1; let y := r.1.2.2.2
  have hm := product_spec hd w.a w.x w.prod1 w.mul1 v u.1 ha hx h1
  have hn := product_spec hd w.quot (pub p) w.prod2 w.mul2 v y.1 hq (fun _ => rfl) h2
  erw [hm1] at hm; erw [hm2] at hn
  have he := sum_spec (by omega : 0 < 2*d) _ _ _ w.carry1 v h2 hr h1
  have hf := sum_spec (by omega : 0 < d+1) _ _ _ w.carry2 v hr hb hs
  have hg := sum_spec (by omega : 0 < d+1) _ _ _ w.carry3 v hz hp hs
  rw [hc1] at he; rw [hc2] at hf; rw [hc3] at hg
  simp only [block,joinB_iff,hm,hn,he,hf,hg,w3_slotHashBits,and_assoc,u,y]

end DetDLP.S8H0.HashRows


