-- Prove2me | Definitions.Def_DetDLP_S8C3_Routes
-- name    : DetDLP_S8C3_Routes
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:12:08.030898+00:00
-- url     : https://prove2.me/theorems/89911d92-bd94-458f-b071-c7ecfb834370
-- title:
--   Tag 3 register bank and declarative row network
-- statement:
--   For width $d\ge 1$, `bank` stores a candidate $x$, one hash run, and the auxiliary bits for the hash, comparison, and nonzero checks. The public parameters $p,T,a,b,\eta$ determine the rows; the register assignment is an input to their acceptance predicate. **Acceptance.** The theorem `network_iff` identifies acceptance with the conjunction of the three residue range checks, the hash block on $(a,x,b,z)$, the strict-comparison certificate for $z<T$, the OR scan starting at zero, and the prefix equality $\operatorname{take}_{|\eta|}(\operatorname{digitWord}_{d-1}(x))=\eta$. The prefix rows read the low $d-1$ bits most significant first, omitting the high padding bit.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_GateRoutes
import Definitions.Def_DetDLP_S8C3_Layout

set_option autoImplicit false
namespace DetDLP.S8C3.Routes
open S8H0 RegisterMap NamedBlocks ResidueWires HashRows S8H.ECPointArithmetic
variable {d e : ℕ}

def bank (d e : ℕ) : Shape := .pair (triple d) (.pair (run d e) (.pair (GateRoutes.auxShape d)
  (.pair (.pair (.word d) (.word (d+1))) (.word d))))
abbrev P (s : Shape) := GateRoutes.Path s (bank d e)
def xp : P (d:=d) (e:=e) (triple d) := Addr.fst
def rp (j : Addr (run d e)) : Addr (bank d e) := .snd (.fst j)
def zp (j : Addr (triple d)) : Addr (bank d e) := rp (.fst j)
def remp (j : Addr (triple d)) : Addr (bank d e) := rp (.snd (.fst (.fst j)))
def auxp (j : Addr (GateRoutes.auxShape d)) : Addr (bank d e) := .snd (.snd (.fst j))
def ltp (j : Addr (.pair (.word d) (.word (d+1)))) : Addr (bank d e) := .snd (.snd (.snd (.fst j)))
def orp (i : Fin d) : Ref (bank d e) := .reg (.snd (.snd (.snd (.snd (.word i)))))
def rw (f : GateRoutes.Path (triple d) (bank d e)) := GateRoutes.word (n:=d) fun j => f (.fst j)
def wires (hd : 1 ≤ d) (p a b : ℕ) : Wires d hd (bank d (w4_M5GraphBounds.graph d hd).nE) :=
  let m1 := fun j => rp (.snd (.fst (.snd (.snd (.fst j)))))
  let m2 := fun j => rp (.snd (.fst (.snd (.snd (.snd j)))))
  { a := pub a, x := rw xp, b := pub b, z := rw zp, rem := rw remp
    quot := GateRoutes.word (n:=d) fun j => rp (.snd (.fst (.snd (.fst j))))
    prod1 := GateRoutes.word (n:=2*d) fun j => m1 (.fst j)
    prod2 := GateRoutes.word (n:=2*d) fun j => m2 (.fst j)
    sum := GateRoutes.word (n:=d+1) fun j => auxp (.snd (.fst j))
    cp := fun i => .masked (p.testBit i) (rp (.snd (.snd .bit)))
    mul1 := fun i => .reg (m1 (.snd (.word i))), mul2 := fun i => .reg (m2 (.snd (.word i)))
    carry1 := fun i => .reg (auxp (.fst (.word i)))
    carry2 := fun i => .reg (auxp (.snd (.snd (.fst (.word i)))))
    carry3 := fun i => .reg (auxp (.snd (.snd (.snd (.word i))))) }

def ltRows (T : ℕ) : B ((bank d e).size+1) := NamedBlocks.add (n:=d+1) true
  (RangeRows.pad fun i : Fin d => .reg (zp (.fst (.word i))))
  (RangeRows.pad fun i : Fin d => .reg (ltp (.fst (.word i))))
  (fun i => .pin (T.testBit i)) (fun i => .reg (ltp (.snd (.word i))))

/-- Each scan step reads the incoming carry, one candidate bit, and the outgoing carry. -/
def scan {s : Shape} : (n : ℕ) → (Fin n → Ref s) → Ref s → (Fin n → Ref s) → B (s.size+1)
  | 0, _, c, _ => rows 1 1 (fun _ _ => c) (fun _ v => v 0)
  | n+1, x, c, t => joinB (rows 1 3 (fun _ => ![c,x 0,t 0])
      (fun _ v => decide (v 2 = (v 0 || v 1)))) (scan n (x ∘ Fin.succ) (t 0) (t ∘ Fin.succ))

theorem scan_iff {s : Shape} (u : Bits (s.size+1)) (n k : ℕ) (x t : Fin n → Ref s) (c : Ref s)
    (h : ∀ i, (x i).eval u = k.testBit i) : (scan n x c t).OK u ↔ w3_slotOr n k (c.eval u) (fun i => (t i).eval u) := by
  induction n generalizing k c with
  | zero => simp [scan, rows_iff, w3_slotOr]
  | succ n ih =>
    simp only [scan, joinB_iff, rows_iff, w3_slotOr.eq_2]
    rw [ih (k/2) (x ∘ Fin.succ) (t ∘ Fin.succ) (t 0) (fun i => (h i.succ).trans (by simp [Nat.testBit_succ]))]
    simp [h, Nat.testBit_zero]

/-- The public digit word omits the high padding bit and is read most significant bit first. -/
def pref (η : List Bool) : B ((bank d e).size+1) := rows η.length 1
  (fun i _ => rw xp (d-2-i.val)) (fun i v => decide (i.val < d-1 ∧ v 0 = η[i]))

def network (hd : 1 ≤ d) (p T a b : ℕ) (η : List Bool) : B ((bank d (w4_M5GraphBounds.graph d hd).nE).size+1) :=
  joinB (RangeRows.checker p xp) <| joinB (RangeRows.checker p zp) <| joinB (RangeRows.checker p remp) <|
  joinB (HashRows.block p (wires hd p a b)) <| joinB (ltRows T) <|
  joinB (scan d (fun i => .reg (xp (.fst (.word i)))) (.pin false) orp) (pref η)

theorem prefix_iff (d k : ℕ) (η : List Bool) : (∀ i : Fin η.length, i.val < d-1 ∧ k.testBit (d-2-i.val) = η[i]) ↔
    (M89S1.digitWord (d-1) k).take η.length = η := by
  rw [eq_comm, ← List.prefix_iff_eq_take, List.prefix_iff_getElem]
  simp only [M89S1.digitWord, List.length_ofFn, List.getElem_ofFn, Fin.rev]
  constructor
  · intro h; refine ⟨?_, fun i hi => ?_⟩
    · by_contra! hn; exact Nat.lt_irrefl _ (h ⟨_,hn⟩).1
    · rw [show d-1-(i+1) = d-2-i by omega]; exact (h ⟨i,hi⟩).2.symm
  · rintro ⟨hl,h⟩ i; refine ⟨lt_of_lt_of_le i.isLt hl, ?_⟩
    rw [show d-2-i.val = d-1-(i.val+1) by omega]; exact (h i i.isLt).symm

theorem network_iff (hd : 1 ≤ d) (p T a b : ℕ) (η : List Bool) (u : Bits ((bank d (w4_M5GraphBounds.graph d hd).nE).size+1)) :
    let v := (bank d (w4_M5GraphBounds.graph d hd).nE).decode (u ∘ Fin.castSucc)
    (network hd p T a b η).OK u ↔ below p v.1 ∧ below p v.2.1.1 ∧ below p v.2.1.2.1.1 ∧
      (HashRows.block p (wires hd p a b)).OK u ∧
      w3_slotLt d (value v.2.1.1.1) T (value v.2.2.2.1.1,v.2.2.2.1.2) ∧
      w3_slotOr d (value v.1.1) false v.2.2.2.2 ∧
      (M89S1.digitWord (d-1) (value v.1.1)).take η.length = η := by
  let s := bank d (w4_M5GraphBounds.graph d hd).nE
  let v := s.decode (u ∘ Fin.castSucc)
  have R (j : Addr s) : (Ref.reg j).eval u = j.get v := (Addr.correct j (u ∘ Fin.castSucc)).symm
  simp only [network, joinB_iff, RangeRows.checker_iff p xp u v.1 (fun j => R (xp j)),
    RangeRows.checker_iff p zp u v.2.1.1 (fun j => R (zp j)),
    RangeRows.checker_iff p remp u v.2.1.2.1.1 (fun j => R (remp j))]
  have X := GateRoutes.word_eval (fun j => xp (.fst j)) u v.1.1 (fun _ => rfl)
  have O := scan_iff u d (value v.1.1) (fun i => .reg (xp (.fst (.word i)))) orp (.pin false)
    (fun i => (R _).trans (value_bit v.1.1 i).symm)
  have C (i : Fin d) : (orp i).eval u = v.2.2.2.2 i := R _
  have E (i : ℕ) : ((rw xp) i).eval u = (value v.1.1).val.testBit i := X i
  rw [O]; simp only [C, pref, rows_iff, decide_eq_true_eq, E]
  have Z := RangeRows.pad_eval (n:=d+1) (fun i => .reg (zp (.fst (.word i)))) u v.2.1.1.1 (fun _ => R _)
  have L := RangeRows.pad_eval (n:=d+1) (fun i => .reg (ltp (.fst (.word i)))) u v.2.2.2.1.1 (fun _ => R _)
  simp only [ltRows, add_iff, Z, L, R, w3_slotLt]
  iterate 4 apply and_congr_right'
  exact and_congr (S8C.AddLayout.columns_iff (Nat.succ_pos d) (value v.2.1.1.1) (value v.2.2.2.1.1) T true v.2.2.2.1.2)
    (and_congr Iff.rfl (prefix_iff d (value v.1.1) η))

end DetDLP.S8C3.Routes


