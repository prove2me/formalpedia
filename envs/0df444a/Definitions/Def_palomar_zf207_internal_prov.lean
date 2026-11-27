-- Prove2me | Definitions.Def_palomar_zf207_internal_prov
-- name    : palomar_zf207_internal_prov
-- status  : Definition
-- author  : @fl-39
-- created : 2026-11-27T00:02:51.020338+00:00
-- url     : https://prove2.me/theorems/1374d67c-5c21-51bf-a5da-94c92f7d9ed5
-- title:
--   Model-internal provability in the Palomar ZF-207 calculus $\mathsf{C}$
-- statement:
--   Relational model-internal formalization of the numeric calculus $\mathsf{C}$ from Section 3 of James Chang's paper inside an arbitrary set-theoretic structure $(V, E)$. Using the internal arithmetic and finite-function primitives of `PalomarZF207History` (`Cantor`, `Add`, `Mul`, `Numeral`, `NatObject`, `FunctionOn`, `At`), this module defines the four formula constructors $\mathsf{I}, \mathsf{M}, \mathsf{U}, \mathsf{E}$, the six logical heads, the restricted propositional head $\rho_8(a,b,c,u)$ ($u \le a$), the pointed-gate axiom $F(a,b,c)$ ($c \neq a, b$), internal finite derivations `InternalCalcDeriv E len f`, and the internal refutation predicate `InternalProvC1 E` asserting the existence of an internal finite $\mathsf{C}$-derivation ending in falsity $1$.
-- source:
--   James Chang, Nonhalting and ZF-independence for a 207-state Turing machine, Section 3 (The calculus), Table 1 and eq. (1)

import Definitions.Def_palomar_zf207_history

namespace PalomarZF207Internal

open PalomarZF207History

section InternalCalc

variable {V : Type} (E : V → V → Prop)

def CalcIc (a b res : V) : Prop :=
  ∃ p four, Cantor E a b p ∧ Numeral E 4 four ∧ Mul E four p res

def CalcMc (a b res : V) : Prop :=
  ∃ ic, CalcIc E a b ic ∧ Succ E ic res

def CalcUc (a B res : V) : Prop :=
  ∃ p four q two, Cantor E B a p ∧ Numeral E 4 four ∧ Mul E four p q ∧ Numeral E 2 two ∧ Add E q two res

def CalcEc (a b res : V) : Prop :=
  ∃ p four q three, Cantor E a b p ∧ Numeral E 4 four ∧ Mul E four p q ∧ Numeral E 3 three ∧ Add E q three res

def CalcNc (B res : V) : Prop :=
  ∃ one, Numeral E 1 one ∧ CalcIc E B one res

def CalcRho8 (a b c u res : V) : Prop :=
  NatObject E a ∧ NatObject E b ∧ NatObject E c ∧ NatObject E u ∧ (E u a ∨ u = a) ∧
  ∃ i1 i2 i3 i4 i5,
    CalcIc E c u i1 ∧ CalcIc E i1 a i2 ∧
    CalcIc E a c i3 ∧ CalcIc E b c i4 ∧
    CalcIc E i3 i4 i5 ∧ CalcIc E i2 i5 res

def CalcHead1 (x y res : V) : Prop :=
  NatObject E x ∧ NatObject E y ∧
  ∃ u1 n1 u2 n2,
    CalcUc E y x u1 ∧ CalcNc E u1 n1 ∧
    CalcUc E y n1 u2 ∧ CalcNc E u2 n2 ∧
    CalcIc E n2 x res

def CalcHead2 (x y z res : V) : Prop :=
  NatObject E x ∧ NatObject E y ∧ NatObject E z ∧
  ∃ u1 u2 u3 u4,
    CalcUc E z x u1 ∧ CalcUc E y u1 u2 ∧
    CalcUc E y x u3 ∧ CalcUc E z u3 u4 ∧
    CalcIc E u2 u4 res

def CalcHead3 (x y z res : V) : Prop :=
  NatObject E x ∧ NatObject E y ∧ NatObject E z ∧
  ∃ m1 e1 m2 i1,
    CalcMc E x y m1 ∧ CalcEc E x z e1 ∧
    CalcMc E z y m2 ∧ CalcIc E e1 m2 i1 ∧
    CalcIc E m1 i1 res

def CalcHead4 (x y z res : V) : Prop :=
  NatObject E x ∧ NatObject E y ∧ NatObject E z ∧
  ∃ e1 m1 m2 i1,
    CalcEc E x y e1 ∧ CalcMc E z x m1 ∧
    CalcMc E z y m2 ∧ CalcIc E m1 m2 i1 ∧
    CalcIc E e1 i1 res

def CalcHead5 (x y res : V) : Prop :=
  NatObject E x ∧ NatObject E y ∧
  ∃ e1 n1 u1,
    CalcEc E x y e1 ∧ CalcNc E e1 n1 ∧
    CalcUc E y n1 u1 ∧ CalcNc E u1 res

def CalcHead6 (x y z res : V) : Prop :=
  NatObject E x ∧ NatObject E y ∧ NatObject E z ∧
  ∃ u1 i1 u2 u3 i2,
    CalcUc E y z u1 ∧ CalcIc E z x i1 ∧
    CalcUc E y i1 u2 ∧ CalcUc E y x u3 ∧
    CalcIc E u2 u3 i2 ∧ CalcIc E u1 i2 res

def CalcGateG (a b c res : V) : Prop :=
  NatObject E a ∧ NatObject E b ∧ NatObject E c ∧
  ∃ m1 m2 i1 subBA m3 n1 i2 u1 stepEx i3 stepAll i4 u2 n2 i5 u3 hullBody i6 lhs i7 rhs,
    CalcMc E c b m1 ∧ CalcMc E c a m2 ∧ CalcIc E m1 m2 i1 ∧ CalcUc E c i1 subBA ∧
    CalcMc E a c m3 ∧ CalcNc E m3 n1 ∧ CalcIc E c n1 i2 ∧ CalcUc E a i2 u1 ∧ CalcNc E u1 stepEx ∧
    CalcIc E c stepEx i3 ∧ CalcUc E a i3 stepAll ∧
    CalcIc E subBA stepAll i4 ∧ CalcUc E b i4 u2 ∧ CalcNc E u2 n2 ∧
    CalcIc E c n2 i5 ∧ CalcUc E b i5 u3 ∧ CalcNc E u3 hullBody ∧
    CalcIc E m3 hullBody i6 ∧ CalcUc E a i6 lhs ∧
    CalcIc E c m3 i7 ∧ CalcNc E i7 rhs ∧
    CalcIc E lhs rhs res

def CalcGateF (a b c res : V) : Prop :=
  NatObject E a ∧ NatObject E b ∧ NatObject E c ∧ c ≠ a ∧ c ≠ b ∧
  ∃ e1 ue1 delta m1 um1 vax g q iq idq,
    CalcEc E a b e1 ∧ CalcUc E c e1 ue1 ∧ CalcIc E e1 ue1 delta ∧
    CalcMc E a b m1 ∧ CalcUc E c m1 um1 ∧ CalcIc E m1 um1 vax ∧
    CalcGateG E a b c g ∧ CalcUc E c g q ∧
    CalcIc E vax q iq ∧ CalcIc E delta iq idq ∧ CalcNc E idq res

def CalcAxiom (x : V) : Prop :=
  Empty E x ∨
  (∃ a b c u, CalcRho8 E a b c u x) ∨
  (∃ a b, CalcHead1 E a b x) ∨
  (∃ a b c, CalcHead2 E a b c x) ∨
  (∃ a b c, CalcHead3 E a b c x) ∨
  (∃ a b c, CalcHead4 E a b c x) ∨
  (∃ a b, CalcHead5 E a b x) ∨
  (∃ a b c, CalcHead6 E a b c x) ∨
  (∃ a b c, CalcGateF E a b c x)

def InternalCalcDeriv (len f : V) : Prop :=
  NatObject E len ∧ ¬ Empty E len ∧ FunctionOn E f len ∧
  (∀ i x, E i len → At E f i x → NatObject E x) ∧
  ∀ i x, E i len → At E f i x →
    CalcAxiom E x ∨
    (∃ j k a imp, E j i ∧ E k i ∧ At E f j a ∧ CalcIc E a x imp ∧ At E f k imp) ∨
    (∃ j a b, E j i ∧ NatObject E a ∧ At E f j b ∧ CalcUc E a b x)

def InternalProvC1 : Prop :=
  ∃ len f last one,
    InternalCalcDeriv E len f ∧ Succ E last len ∧ Numeral E 1 one ∧ At E f last one

end InternalCalc

end PalomarZF207Internal


