-- Prove2me | Definitions.Def_DetDLP_S8H0_CurveRows
-- name    : DetDLP_S8H0_CurveRows
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:19:17.946158+00:00
-- url     : https://prove2.me/theorems/227a0b0d-d617-4b1d-a593-bffbd2991d6f
-- title:
--   Bitwise curve equality and infinity rows
-- statement:
--   The check uses five incident bits per word digit. For the infinity flag the coordinate bits must both vanish, and otherwise bits of gate outputs two and five must agree. Acceptance is precisely the corresponding condition on the decoded words.
-- source:
--   DetDLP.s8h_ec_order_query, f0e81f0e-6143-4672-a126-0c2b5aa2d552.

import Definitions.Def_DetDLP_S8H0_NamedBlocks

set_option autoImplicit false
namespace DetDLP.S8H0.CurveRows
open S8H.ECPointArithmetic S8H.ECPointSlots RegisterMap ResidueWires NamedBlocks SignalBank

variable {d e : ℕ}

def flag : Addr (bank d e) := .fst (.fst .bit)
def xbit (i : Fin d) : Addr (bank d e) := .fst (.snd (.fst (.fst (.word i))))
def ybit (i : Fin d) : Addr (bank d e) := .fst (.snd (.snd (.fst (.word i))))
def outbit (g : Fin 7) (i : Fin d) : Addr (bank d e) := .snd (.fst (.vec g (.fst (.fst (.word i)))))

def refs (i : Fin d) : Fin 5 → Ref (bank d e) := ![.reg flag,.reg (xbit i),.reg (ybit i),.reg (outbit 2 i),.reg (outbit 5 i)]

def test (f x y l r : Bool) := if f then decide (x = false ∧ y = false) else decide (l = r)
def check (a : Fin 5 → Bool) := test (a 0) (a 1) (a 2) (a 3) (a 4)

def block (d e : ℕ) := rows d 5 (@refs d e) (fun _ => check)

private def choose (f : Bool) (a b : Prop) := if f then a else b
def rawCheck (v : (bank d e).Data) :=
  choose v.1.1 (value v.1.2.1.1 = 0 ∧ value v.1.2.2.1 = 0)
    (value (v.2.1 2).1.1 = value (v.2.1 5).1.1)

private theorem zero_bits (w : Bits d) : (∀ i, w i = false) ↔ value w = 0 := by
  constructor
  · intro h
    apply (numBits d).symm.injective; funext i
    change (value w).val.testBit _ = (0:ℕ).testBit _
    simp [h]
  · intro h i; have he := value_bit w i; rw [h] at he; simpa using he.symm

theorem block_iff (u : Bits ((bank d e).size+1)) :
    (block d e).OK u ↔ rawCheck ((bank d e).decode (u ∘ Fin.castSucc)) := by
  let v := (bank d e).decode (u ∘ Fin.castSucc)
  have hr (r : Ref (bank d e)) : r.eval u = r.data v := (r.correct u).symm
  change (rows d 5 _ _).OK u ↔ rawCheck v
  rw [rows_iff]; simp_rw [hr]
  change (∀ i : Fin d, test v.1.1 (v.1.2.1.1 i) (v.1.2.2.1 i) ((v.2.1 2).1.1 i) ((v.2.1 5).1.1 i) = true) ↔ rawCheck v
  unfold rawCheck choose test
  cases h : v.1.1
  · simp only [Bool.false_eq_true,if_false,decide_eq_true_eq]
    exact ⟨fun H => congrArg value (funext H),fun H => congrFun ((numBits d).injective H)⟩
  · simp only [if_true,decide_eq_true_eq,forall_and]
    exact and_congr (zero_bits (d:=d) v.1.2.1.1) (zero_bits (d:=d) v.1.2.2.1)

end DetDLP.S8H0.CurveRows


