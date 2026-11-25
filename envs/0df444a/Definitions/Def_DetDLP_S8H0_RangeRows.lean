-- Prove2me | Definitions.Def_DetDLP_S8H0_RangeRows
-- name    : DetDLP_S8H0_RangeRows
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:17:55.921041+00:00
-- url     : https://prove2.me/theorems/4d919234-3762-4f76-b231-d8f95f5cd3d7
-- title:
--   Sixteen wired canonical-residue comparisons
-- statement:
--   Wires the three words of each residue to a comparison adder. The conjunction for the two coordinates and the fourteen output and remainder registers accepts exactly the canonical Boolean assignments.
-- source:
--   DetDLP.s8h_ec_order_query, f0e81f0e-6143-4672-a126-0c2b5aa2d552.

import Definitions.Def_DetDLP_S8H0_NamedBlocks

set_option autoImplicit false
namespace DetDLP.S8H0.RangeRows
open RegisterMap NamedBlocks ResidueWires SignalBank

variable {d e : ℕ} {s : Shape}

def pad {n : ℕ} (f : Fin d → Ref s) (i : Fin n) : Ref s :=
  if h : i.val < d then f ⟨i.val,h⟩ else .pin false

theorem pad_eval {n : ℕ} (f : Fin d → Ref s) (x : Bits (s.size+1)) (z : Bits d)
    (h : ∀ i, (f i).eval x = z i) (i : Fin n) :
    (pad f i).eval x = (value z).val.testBit i.val := by
  unfold pad; split
  · rename_i hi; exact (h ⟨i.val,hi⟩).trans (value_bit z ⟨i.val,hi⟩).symm
  · rename_i hi; exact (Nat.testBit_lt_two_pow ((value z).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega : d ≤ i.val)))).symm

def checker (p : ℕ) (addr : Addr (triple d) → Addr s) :=
  add (n:=d+1) true (pad (fun i => .reg (addr (.fst (.word i)))))
    (pad (fun i => .reg (addr (.snd (.fst (.word i)))))) (fun i => .pin (p.testBit i.val))
    (fun i => .reg (addr (.snd (.snd (.word i)))))

theorem checker_iff (p : ℕ) (addr : Addr (triple d) → Addr s) (x : Bits (s.size+1)) (w : Triple d)
    (h : ∀ j : Addr (triple d), (Ref.reg (addr j)).eval x = j.get w) :
    (checker p addr).OK x ↔ below p w := by
  unfold checker; erw [add_iff]
  let L := fun i : Fin d => Ref.reg (addr (.fst (.word i)))
  let R := fun i : Fin d => Ref.reg (addr (.snd (.fst (.word i))))
  have hl := pad_eval (n:=d+1) L x w.1 (fun i => h _)
  have hr := pad_eval (n:=d+1) R x w.2.1 (fun i => h _)
  have hc (i : Fin (d+1)) : (Ref.reg (addr (.snd (.snd (.word i))))).eval x = w.2.2 i := h _
  change S8C.AddLayout.Columns true (fun i => (pad L i).eval x) (fun i => (pad R i).eval x) (fun i => p.testBit i.val) _ ↔ _
  simp only [hl,hr,hc]
  exact (S8C.AddLayout.columns_iff (by omega : 0 < d+1) ..).trans (below_iff p w).symm

def many {k : ℕ} : (n : ℕ) → (Fin (n+1) → B k) → B k
  | 0,f => f 0
  | n+1,f => joinB (f 0) (many n (fun i => f i.succ))

theorem many_iff {k : ℕ} (n : ℕ) (f : Fin (n+1) → B k) (x : Bits k) :
    (many n f).OK x ↔ ∀ i, (f i).OK x := by
  induction n with
  | zero =>
    refine ⟨fun h i => ?_, fun h => h 0⟩
    obtain rfl : i = 0 := Fin.ext (by omega); exact h
  | succ n ih => rw [many,joinB_iff,ih]; exact ⟨fun h i => Fin.cases h.1 h.2 i,fun h => ⟨h 0,fun i => h i.succ⟩⟩

def xa (a : Addr (triple d)) : Addr (bank d e) := .fst (.snd (.fst a))
def ya (a : Addr (triple d)) : Addr (bank d e) := .fst (.snd (.snd a))
def oa (i : Fin 7) (a : Addr (triple d)) : Addr (bank d e) := .snd (.fst (.vec i (.fst a)))
def ra (i : Fin 7) (a : Addr (triple d)) : Addr (bank d e) := .snd (.fst (.vec i (.snd (.fst (.fst a)))))

def block (d e p : ℕ) : B ((bank d e).size+1) :=
  joinB (joinB (checker p xa) (checker p ya)) (many 6 fun i => joinB (checker p (oa i)) (checker p (ra i)))

theorem block_iff (p : ℕ) (x : Bits ((bank d e).size+1)) : let v := (bank d e).decode (x ∘ Fin.castSucc)
    (block d e p).OK x ↔ (below p v.1.2.1 ∧ below p v.1.2.2) ∧ ∀ i, below p (v.2.1 i).1 ∧ below p (v.2.1 i).2.1.1 := by
  let v := (bank d e).decode (x ∘ Fin.castSucc)
  have h (a : Addr (bank d e)) : (Ref.reg a).eval x = a.get v := (Addr.correct a (x ∘ Fin.castSucc)).symm
  have hx := checker_iff p (@xa d e) x v.1.2.1 (fun a => h _)
  have hy := checker_iff p (@ya d e) x v.1.2.2 (fun a => h _)
  have ho (i : Fin 7) := checker_iff p (@oa d e i) x (v.2.1 i).1 (fun a => h _)
  have hr (i : Fin 7) := checker_iff p (@ra d e i) x (v.2.1 i).2.1.1 (fun a => h _)
  simp only [block,joinB_iff,many_iff,hx,hy,ho,hr,v]

end DetDLP.S8H0.RangeRows


