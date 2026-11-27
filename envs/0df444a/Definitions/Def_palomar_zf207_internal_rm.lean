-- Prove2me | Definitions.Def_palomar_zf207_internal_rm
-- name    : palomar_zf207_internal_rm
-- status  : Definition
-- author  : @fl-39
-- created : 2026-11-27T04:19:30.724026+00:00
-- url     : https://prove2.me/theorems/f1cc404a-aca1-4e43-af30-4e5c1ff2790a
-- title:
--   Model-internal register-machine reachability and instruction semantics for the 207-state TM
-- statement:
--   Defines the model-internal register-machine abstraction layer for the 207-state Turing machine inside an arbitrary model $(V, E)$ of $\mathrm{ZF}$. Given a $9$-tuple of registers $r = (r_0, \dots, r_8) \in (\omega^V)^9$ and $42$-bit program-counter prefixes $p_1, p_2 \in \{0,1\}^{42}$, we define:
--
--   - Register lookup $\mathrm{regGetV}(k, r)$ and update $\mathrm{regSetV}(k, v, r)$ for $0 \le k < 9$.
--   - Model-internal register reachability $\mathrm{RegReachV}_E(p_1, r, p_2, r')$, asserting that from every valid encoded register frame with positive gap $m \ge 1$ and positive trailing garbage $t \ge 1$, the Turing machine internally reaches a valid encoded register frame at $(p_2, r')$ with positive $m', t' \ge 1$.
--   - Model-internal register halting $\mathrm{RegHaltsV}_E(p, r)$, asserting that every valid encoded register frame at $(p, r)$ with $m, t \ge 1$ internally reaches a terminal (halting) configuration.
--   - The instruction-level soundness interface $\mathrm{InternalRegMachine}_E$, stating that `decodeLBits` accurately reflects goto, increment, decrement (nonzero and zero branches), and halt instructions inside $(V, E)$.
-- source:
--   James Chang, Nonhalting and ZF-independence for a 207-state Turing machine, Sections 2 and 6 (register-machine compilation and simulation inside models of ZF)

import Definitions.Def_palomar_zf207_tm_check
import Definitions.Def_palomar_zf207_internal_tm

namespace PalomarZF207InternalRM

open PalomarZF207History
open PalomarZF207Internal
open PalomarZF207InternalTM
open PalomarZF207TMCheck

/-- Read register `k` (`0 ≤ k < 9`) from a 9-register tuple in a model. -/
def regGetV {V : Type} (k : Nat) (rs : Regs9 V) : V :=
  match k with
  | 0 => rs.r0
  | 1 => rs.r1
  | 2 => rs.r2
  | 3 => rs.r3
  | 4 => rs.r4
  | 5 => rs.r5
  | 6 => rs.r6
  | 7 => rs.r7
  | _ => rs.r8

/-- Update register `k` (`0 ≤ k < 9`) in a 9-register tuple in a model. -/
def regSetV {V : Type} (k : Nat) (val : V) (rs : Regs9 V) : Regs9 V :=
  match k with
  | 0 => { rs with r0 := val }
  | 1 => { rs with r1 := val }
  | 2 => { rs with r2 := val }
  | 3 => { rs with r3 := val }
  | 4 => { rs with r4 := val }
  | 5 => { rs with r5 := val }
  | 6 => { rs with r6 := val }
  | 7 => { rs with r7 := val }
  | _ => { rs with r8 := val }

/-- Internal reachability between register-machine configurations over any valid margin `m ≥ 1` and tail `t ≥ 1`. -/
def RegReachV {V : Type} (E : V → V → Prop)
    (p1 : List Bool) (rs1 : Regs9 V) (p2 : List Bool) (rs2 : Regs9 V) : Prop :=
  ∀ m t code, ¬ Empty E m → ¬ Empty E t →
    FrameCodeV E (bitsToNat p1) m rs1 t code →
    ∃ m' t' code', ¬ Empty E m' ∧ ¬ Empty E t' ∧
      FrameCodeV E (bitsToNat p2) m' rs2 t' code' ∧
      InternalReach E code code'

/-- Internal halting from a register-machine configuration over any valid margin `m ≥ 1` and tail `t ≥ 1`. -/
def RegHaltsV {V : Type} (E : V → V → Prop)
    (p : List Bool) (rs : Regs9 V) : Prop :=
  ∀ m t code, ¬ Empty E m → ¬ Empty E t →
    FrameCodeV E (bitsToNat p) m rs t code →
    InternalHaltsFrom E code

/-- Internal register-machine instruction semantics for the 207-state TM's `decodeLBits` decoder. -/
def InternalRegMachine {V : Type} (E : V → V → Prop) : Prop :=
  ∀ (pref : List Bool) (rs : Regs9 V),
    pref.length = 42 → Regs9Nat E rs →
    (∀ pn, decodeLBits pref = .goto pn →
      pn.length = 42 ∧ RegReachV E pref rs pn rs) ∧
    (∀ k pn, decodeLBits pref = .inc k pn →
      k < 9 ∧ pn.length = 42 ∧
      ∀ v', Succ E (regGetV k rs) v' → RegReachV E pref rs pn (regSetV k v' rs)) ∧
    (∀ k pnz pz, decodeLBits pref = .dec k pnz pz →
      k < 9 ∧ pnz.length = 42 ∧ pz.length = 42 ∧
      (∀ v', Succ E v' (regGetV k rs) → RegReachV E pref rs pnz (regSetV k v' rs)) ∧
      (Empty E (regGetV k rs) → RegReachV E pref rs pz rs)) ∧
    (decodeLBits pref = .halt → RegHaltsV E pref rs)

end PalomarZF207InternalRM


