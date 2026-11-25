-- Prove2me | Definitions.Def_DetDLP_S8H0_GateRoutes
-- name    : DetDLP_S8H0_GateRoutes
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:32:52.662456+00:00
-- url     : https://prove2.me/theorems/2c61444c-dd75-4b1d-9493-96ceb4ec4bb9
-- title:
--   Operand routes for elliptic-curve point checks
-- statement:
--   Concrete register addresses wire the sixteen range tests, seven multiply-add tests, coefficients, and final curve rows into a single occurrence layout.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_HashRows
import Definitions.Def_DetDLP_S8H0_CurveRows

set_option autoImplicit false
namespace DetDLP.S8H0.GateRoutes
open RegisterMap NamedBlocks ResidueWires SignalBank HashRows RangeRows S8H.ECPointArithmetic

variable {d e : ℕ}
abbrev S (d e : ℕ) := bank d e
abbrev Path (u v : Shape) := Addr u → Addr v

def word {n : ℕ} {s : Shape} (a : Path (.word n) s) : Word s := padded fun j => .reg (a (.word j))
def rword (a : Path (triple d) (S d e)) : Word (S d e) := word fun j => a (.fst j)
def runPath (g : Fin 7) (a : Addr (run d e)) : Addr (S d e) := .snd (.fst (.vec g a))
def quot (g : Fin 7) : Word (S d e) := word (n:=d) fun a => runPath g (.snd (.fst (.snd (.fst a))))
def m1 (g : Fin 7) (a : Addr (RegisterMap.mul d e)) : Addr (S d e) := runPath g (.snd (.fst (.snd (.snd (.fst a)))))
def m2 (g : Fin 7) (a : Addr (RegisterMap.mul d e)) : Addr (S d e) := runPath g (.snd (.fst (.snd (.snd (.snd a)))))
def cm (g : Fin 7) : Addr (S d e) := runPath g (.snd (.snd .bit))
def auxShape (d : ℕ) := Shape.pair (.word (2*d)) (.pair (.word (d+1)) (.pair (.word (d+1)) (.word (d+1))))
def aux (g : Fin 7) (a : Addr (auxShape d)) : Addr (S d e) := .snd (.snd (.vec g a))

structure Coeff where
  a1 : ℕ
  a2 : ℕ
  a3 : ℕ
  a4 : ℕ
  a6 : ℕ

def operands (c : Coeff) (i : Fin 7) : Word (S d e) × Word (S d e) × Word (S d e) :=
  let X := rword (d:=d) (e:=e) xa; let Y := rword (d:=d) (e:=e) ya
  let O := fun g => rword (d:=d) (e:=e) (oa g)
  ![(pub c.a1,X,Y),(pub 1,O 0,pub c.a3),(O 1,Y,pub 0),(pub 1,X,pub c.a2),
    (O 3,X,pub c.a4),(O 4,X,pub c.a6),(pub 0,X,pub 0)] i

def wires (hd : 1 ≤ d) (p : ℕ) (c : Coeff) (g : Fin 7) : Wires d hd (S d (w4_M5GraphBounds.graph d hd).nE) where
  a := (operands c g).1
  x := (operands c g).2.1
  b := (operands c g).2.2
  z := rword (oa g)
  rem := rword (ra g)
  quot := quot g
  prod1 := word (n:=2*d) fun a => m1 g (.fst a)
  prod2 := word (n:=2*d) fun a => m2 g (.fst a)
  sum := word (n:=d+1) fun a => aux g (.snd (.fst a))
  cp := fun i => .masked (p.testBit i) (cm g)
  mul1 := fun i => .reg (m1 g (.snd (.word i)))
  mul2 := fun i => .reg (m2 g (.snd (.word i)))
  carry1 := fun i => .reg (aux g (.fst (.word i)))
  carry2 := fun i => .reg (aux g (.snd (.snd (.fst (.word i)))))
  carry3 := fun i => .reg (aux g (.snd (.snd (.snd (.word i)))))

def network (hd : 1 ≤ d) (p : ℕ) (c : Coeff) :=
  let e := (w4_M5GraphBounds.graph d hd).nE
  let arith := many 6 fun g => HashRows.block p (wires hd p c g)
  joinB (RangeRows.block d e p) (joinB arith (CurveRows.block d e))

theorem network_iff (hd : 1 ≤ d) (p : ℕ) (c : Coeff) (x : Bits ((S d (w4_M5GraphBounds.graph d hd).nE).size+1)) :
    let v := (S d (w4_M5GraphBounds.graph d hd).nE).decode (x ∘ Fin.castSucc)
    (network hd p c).OK x ↔ canonical p v ∧ (∀ g, (HashRows.block p (wires hd p c g)).OK x) ∧ CurveRows.rawCheck v := by
  simp only [network,joinB_iff,many_iff,RangeRows.block_iff,CurveRows.block_iff,canonical]

theorem word_eval {s : Shape} {n : ℕ} (a : Path (.word n) s) (u : Bits (s.size+1)) (w : Bits n)
    (h : ∀ i : Fin n, (a (.word i)).get (s.decode (u ∘ Fin.castSucc)) = w i) : evalWord (word a) u (value w).val :=
  padded_spec _ u w fun i => (Addr.correct (a (.word i)) (u ∘ Fin.castSucc)).symm.trans (h i)

end DetDLP.S8H0.GateRoutes


