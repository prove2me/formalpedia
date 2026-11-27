-- Prove2me | Definitions.Def_palomar_zf207_internal_tm
-- name    : palomar_zf207_internal_tm
-- status  : Definition
-- author  : @fl-39
-- created : 2026-11-27T03:19:11.322222+00:00
-- url     : https://prove2.me/theorems/dcc31c8c-4cc8-448a-bd6e-4f7868cd42d1
-- title:
--   Model-internal execution and register-frame semantics for the 207-state Turing machine
-- statement:
--   Model-internal execution and register-machine frame predicates for the 207-state Turing machine inside an arbitrary set-theoretic structure $(V, E)$.
--
--   This module defines:
--
--   1. Internally finite transition sequences $\mathrm{InternalStepSeq}_E(n, c_1, c_2)$ of length $n \in \omega^V$, reachability $\mathrm{InternalReach}_E(c_1, c_2)$, and halting $\mathrm{InternalHaltsFrom}_E(c)$ to a terminal configuration.
--   2. Internal binary tape arithmetic $\mathrm{Pow2}_E(n, 2^n)$, $\mathrm{Ones}_E(n, 2^n-1)$, $\mathrm{TailBitsV}_E(t, \mathrm{tail}(t))$, and unary register blocks $\mathrm{RegBlockV}_E(v, s, 2((2^{v+1}-1)+2^{v+1}s))$.
--   3. Clean register-machine frames $\mathrm{FrameCodeV}_E(\mathrm{pref}, m, \vec{r}, t, c)$ encoding the configuration $(74, 1, \mathrm{pref} + 2^{42+m}\cdot \mathrm{regsBits}(\vec{r}, t))$ for a 9-register state $\vec{r} = (r_0, \dots, r_8)$ inside $(V, E)$.
--   4. The one-iteration register-machine transition specification $\mathrm{InternalLoopStep}_E$ at the main loop header $\mathrm{pref}=1$, capturing scheduler counter reload, the shift/halt check ($\mathrm{op}=0$), modus ponens ($\mathrm{op}=1$), and universal generalization plus all axiom schemas of calculus $\mathsf{C}$ ($\mathrm{op}=z+2$).
--
--   These predicates cleanly decouple the low-level tape simulation of the literal 207-state table from the high-level proof-search completeness argument inside models of $\mathrm{ZF}$.
-- source:
--   James Chang, Nonhalting and ZF-independence for a 207-state Turing machine, Sections 2 and 6 (Lemma 6.1, internalized machine completeness)

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_internal_prov

namespace PalomarZF207InternalTM

open PalomarZF207History
open PalomarZF207Internal

section InternalTM

variable {V : Type} (E : V → V → Prop)

/-- Internal finite execution sequence of length `n` from configuration code `c1` to `c2`. -/
def InternalStepSeq (n c1 c2 : V) : Prop :=
  NatObject E n ∧ NatObject E c1 ∧ NatObject E c2 ∧
  ∃ z dom f, Empty E z ∧ Succ E n dom ∧ FunctionOn E f dom ∧
    At E f z c1 ∧ At E f n c2 ∧
    (∀ i x, E i dom → At E f i x → NatObject E x) ∧
    ∀ i, E i n → ∃ j x y, Succ E i j ∧ At E f i x ∧ At E f j y ∧ NumericStep E x y

/-- Internal finite reachability between configuration codes. -/
def InternalReach (c1 c2 : V) : Prop :=
  ∃ n, InternalStepSeq E n c1 c2

/-- Internal halting from configuration code `c`. -/
def InternalHaltsFrom (c : V) : Prop :=
  ∃ c', ∃ (t : Conf V), InternalReach E c c' ∧ NumericConfCode E t c' ∧ Valid E t ∧ Terminal E t

/-- Internal exponentiation `res = 2^n`. -/
def Pow2 (n res : V) : Prop :=
  NatObject E n ∧ NatObject E res ∧
  ∃ z one two dom f, Empty E z ∧ Numeral E 1 one ∧ Numeral E 2 two ∧
    Succ E n dom ∧ FunctionOn E f dom ∧
    At E f z one ∧ At E f n res ∧
    (∀ i x, E i dom → At E f i x → NatObject E x) ∧
    ∀ i, E i n → ∃ j x y, Succ E i j ∧ At E f i x ∧ At E f j y ∧ Mul E two x y

/-- Internal all-ones mask `res = 2^n - 1`. -/
def Ones (n res : V) : Prop :=
  NatObject E n ∧ NatObject E res ∧
  ∃ p one, Pow2 E n p ∧ Numeral E 1 one ∧ Add E res one p

/-- Internal trailing garbage tape encoding `tailBits t` (`0 ↦ 0`, `t+1 ↦ 6 + 8 * tailBits t`). -/
def TailBitsV (t res : V) : Prop :=
  NatObject E t ∧ NatObject E res ∧
  ∃ z six eight dom f, Empty E z ∧ Numeral E 6 six ∧ Numeral E 8 eight ∧
    Succ E t dom ∧ FunctionOn E f dom ∧
    At E f z z ∧ At E f t res ∧
    (∀ i x, E i dom → At E f i x → NatObject E x) ∧
    ∀ i, E i t → ∃ j x y p, Succ E i j ∧ At E f i x ∧ At E f j y ∧ Mul E eight x p ∧ Add E six p y

/-- Internal single register block `2 * ((2^(v+1) - 1) + 2^(v+1) * suf)`. -/
def RegBlockV (v suf res : V) : Prop :=
  NatObject E v ∧ NatObject E suf ∧ NatObject E res ∧
  ∃ vs o p two prod sum,
    Succ E v vs ∧ Ones E vs o ∧ Pow2 E vs p ∧ Numeral E 2 two ∧
    Mul E p suf prod ∧ Add E o prod sum ∧ Mul E two sum res

/-- Nine register values inside a set-theoretic model. -/
structure Regs9 (W : Type) where
  r0 : W
  r1 : W
  r2 : W
  r3 : W
  r4 : W
  r5 : W
  r6 : W
  r7 : W
  r8 : W

def Regs9Nat (rs : Regs9 V) : Prop :=
  NatObject E rs.r0 ∧ NatObject E rs.r1 ∧ NatObject E rs.r2 ∧
  NatObject E rs.r3 ∧ NatObject E rs.r4 ∧ NatObject E rs.r5 ∧
  NatObject E rs.r6 ∧ NatObject E rs.r7 ∧ NatObject E rs.r8

/-- Internal right-tape encoding of the 9 registers and trailing garbage `t`. -/
def RegsBitsV (rs : Regs9 V) (t res : V) : Prop :=
  ∃ s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 one two prod,
    TailBitsV E t s9 ∧
    RegBlockV E rs.r8 s9 s8 ∧ RegBlockV E rs.r7 s8 s7 ∧ RegBlockV E rs.r6 s7 s6 ∧
    RegBlockV E rs.r5 s6 s5 ∧ RegBlockV E rs.r4 s5 s4 ∧ RegBlockV E rs.r3 s4 s3 ∧
    RegBlockV E rs.r2 s3 s2 ∧ RegBlockV E rs.r1 s2 s1 ∧ RegBlockV E rs.r0 s1 s0 ∧
    Numeral E 1 one ∧ Numeral E 2 two ∧ Mul E two s0 prod ∧ Add E one prod res

/-- Internal configuration code of clean register frame `(74, 1, pref + 2^(42 + m) * regsBits rs t)`. -/
def FrameCodeV (pref : Nat) (m : V) (rs : Regs9 V) (t code : V) : Prop :=
  NatObject E m ∧ NatObject E t ∧ Regs9Nat E rs ∧
  ∃ q74 one p42 prefV exp pexp rb prod rightV,
    Numeral E 74 q74 ∧ Numeral E 1 one ∧ Numeral E 42 p42 ∧ Numeral E pref prefV ∧
    Add E p42 m exp ∧ Pow2 E exp pexp ∧ RegsBitsV E rs t rb ∧
    Mul E pexp rb prod ∧ Add E prefV prod rightV ∧
    NumericConfCode E ⟨q74, one, rightV⟩ code

/-- Exact one-iteration register-machine semantics of the 207-state TM at loop header `pref = 1`. -/
def InternalLoopStep : Prop :=
  ∀ (r0 r1 r2 r3 r6 r7 m t z code : V),
    NatObject E r0 → NatObject E r1 → NatObject E r2 → NatObject E r3 →
    NatObject E r6 → NatObject E r7 → NatObject E m → NatObject E t →
    Empty E z → ¬ Empty E m → ¬ Empty E t →
    FrameCodeV E 1 m ⟨r0, r1, r2, r3, z, z, r6, r7, z⟩ t code →
    ∀ (w ctr op w' : V),
      ((Empty E r1 ∧ w = r6 ∧ Succ E r6 ctr) ∨ (Succ E w r1 ∧ ctr = r6)) →
      Cantor E op w' w →
      (Empty E op →
        ∀ (s27 one : V), Add E r2 r7 s27 → Numeral E 1 one →
          (s27 = one → InternalHaltsFrom E code) ∧
          (s27 ≠ one → ∀ (hd tl : V), Cantor E hd tl r0 →
            ∃ m' t' code', ¬ Empty E m' ∧ ¬ Empty E t' ∧
              FrameCodeV E 1 m' ⟨tl, w', r7, r3, z, z, ctr, hd, z⟩ t' code' ∧
              InternalReach E code code')) ∧
      (Numeral E 1 op →
        ∀ (b w2 B ic : V), Cantor E b w2 w' → Add E r3 b B → CalcIc E r2 B ic →
          (r7 = ic → ∀ (s0 : V), Cantor E z r0 s0 →
            ∃ m' t' code', ¬ Empty E m' ∧ ¬ Empty E t' ∧
              FrameCodeV E 1 m' ⟨s0, w2, B, B, z, z, ctr, z, z⟩ t' code' ∧
              InternalReach E code code') ∧
          (r7 ≠ ic →
            ∃ m' t' code', ¬ Empty E m' ∧ ¬ Empty E t' ∧
              FrameCodeV E 1 m' ⟨r0, w2, z, B, z, z, ctr, z, z⟩ t' code' ∧
              InternalReach E code code')) ∧
      (∀ (opZ op1 : V), Succ E opZ op1 → Succ E op1 op →
        ∀ (x w1 y w2 X Y : V),
          Cantor E x w1 w' → Cantor E y w2 w1 → Add E r7 x X → Add E r3 y Y →
          ∀ (uc r8 h1 h2 h3 h4 h5 h6 s1 s2 s3 s4 s5 s6 s7 s8 s9 top : V),
            CalcUc E r3 r7 uc → CalcRho8 E Y opZ X r3 r8 →
            CalcHead1 E X Y h1 → CalcHead2 E X Y opZ h2 → CalcHead3 E X Y opZ h3 →
            CalcHead4 E X Y opZ h4 → CalcHead5 E X Y h5 → CalcHead6 E X Y opZ h6 →
            Cantor E r2 r0 s1 → Cantor E uc s1 s2 → Cantor E r8 s2 s3 →
            Cantor E h1 s3 s4 → Cantor E h2 s4 s5 → Cantor E h3 s5 s6 →
            Cantor E h4 s6 s7 → Cantor E h5 s7 s8 → Cantor E h6 s8 s9 →
            ((opZ ≠ X ∧ opZ ≠ Y ∧ CalcGateF E X Y opZ top) ∨
             ((opZ = X ∨ opZ = Y) ∧ Empty E top)) →
            ∃ m' t' code', ¬ Empty E m' ∧ ¬ Empty E t' ∧
              FrameCodeV E 1 m' ⟨s9, w2, top, z, z, z, ctr, z, z⟩ t' code' ∧
              InternalReach E code code')

end InternalTM

end PalomarZF207InternalTM


