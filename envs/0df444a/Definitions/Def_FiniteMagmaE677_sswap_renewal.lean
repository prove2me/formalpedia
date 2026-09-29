-- Prove2me | Definitions.Def_FiniteMagmaE677_sswap_renewal
-- name    : FiniteMagmaE677_sswap_renewal
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-24T08:33:34.79396+00:00
-- url     : https://prove2.me/theorems/ebd9f39e-2b7d-4d59-9a78-21b48364bca5
-- title:
--   D4 swapped-S renewal, q-square refinement, and cycle accounting
-- statement:
--   Let $L_x(y)=x\diamond y$. This interface describes the swapped-S branch of the period-four analysis of E677. It retains the distinguished four-cycle, the swapped pair $q,s$, a fresh initialized $t$-cycle, the bridge equation, and the three cross-cycle alternatives. Renewal records preserve the explicit fixer $p=q\diamond(q\diamond x)$ at $q$ and its partner $u=q\diamond p$.
--
--   The one-step packet classifies $p,u$ relative to the exact finite cycles, retaining all five contact or escape alternatives. The q-square refinement puts $v=q\diamond q$ and records freshness, $p=u\diamond v$, and the oriented phase relations or new cycles. Finite cycle sets and marked-phase slack are also defined. These are data types and predicates, not an assertion that any branch closes or can be iterated.
-- source:
--   https://github.com/flound1129/the-missing-pair/tree/f9945b937be61f4ca48eb6cafdcfa07ba7a7f78c/lean/E677/Spine ; Piece1D4SSwapCycleReduction, CommonRenewal, CycleAccounting, QFixerPump, QSquareRenewal, PNewQSquareRenewal. Explicit-operation adapters use the previously published D4 definitions.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib
import Definitions.Def_FiniteMagmaE677_d4_first_return
import Definitions.Def_FiniteMagmaE677_seventh_element_growth

section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna.
-/

/-!
# S-swap source compatibility surface

The source S-swap fragments use a class-local operation.  This module keeps
that notation isolated while reusing the published trace and first-return definitions. The
distinguished packet is a field-level projection of the source wrapper; the
S-tagged start retains the branch facts needed by this package.
-/

namespace FiniteMagmaE677.SSwap

universe u

class Magma' (α : Type u) where
  op : α → α → α

local infixl:65 " ◇ " => Magma'.op

abbrev E677 (α : Type u) [Magma' α] : Prop :=
  FiniteMagmaE677.E677 (Magma'.op (α := α))

abbrev D4LeftTrace {α : Type u} [Magma' α]
    (x c1 c2 c3 seed : α) (n : ℕ) : Prop :=
  FiniteMagmaE677.FirstReturn.D4Trace (Magma'.op (α := α))
    x c1 c2 c3 seed n

abbrev D4LeftFirstReturn {α : Type u} [Magma' α]
    (x c1 c2 c3 seed : α) (n : ℕ) : Type :=
  FiniteMagmaE677.FirstReturn.D4FirstReturn (Magma'.op (α := α))
    x c1 c2 c3 seed n

abbrev E677FreshOutsideSix {α : Type u} [Magma' α]
    (x c1 c2 c3 q s t : α) : Prop :=
  FiniteMagmaE677.FreshOutsideSix (Magma'.op (α := α))
    x c1 c2 c3 q s t

abbrev E677D4QDistinguishedPacket {α : Type u} [Magma' α]
    (x c1 c2 c3 : α) : Prop :=
  FiniteMagmaE677.FirstReturn.D4Distinguished (Magma'.op (α := α))
    x c1 c2 c3

abbrev E677D4QSTaggedTraceStart {α : Type u} [Magma' α]
    (x c1 c2 c3 : α) : Prop :=
  FiniteMagmaE677.FirstReturn.STaggedStart (Magma'.op (α := α))
    x c1 c2 c3

end FiniteMagmaE677.SSwap
end

section
/-
Pure S-swap renewal declarations.  The assembler supplies the platform header,
the explicit-operation aliases, and imports; this fragment has no research
imports and contains no proof obligations.
-/

namespace FiniteMagmaE677.SSwap
local infixl:65 " ◇ " => Magma'.op

universe u

variable {α : Type u} [Magma' α]

def LxPhase (x t : α) (k : ℕ) : α :=
  ((fun z : α ↦ x ◇ z)^[k]) t

structure D4SSwapDualCollision (x c1 c2 c3 q s t : α) : Prop where
  t_c3_eq_q : t ◇ c3 = q
  q_t_eq_c1 : q ◇ t = c1
  c1_s_eq_t : c1 ◇ s = t
  c2_s_eq_t : c2 ◇ s = t

structure D4SSwapPositivePhaseContact
    (x c1 c2 c3 t : α)
    (first : D4LeftFirstReturn x c1 c2 c3 t 0) : Type u where
  phase : ℕ
  phase_pos : 0 < phase
  phase_lt : phase < first.period
  t_c3_eq_phase : t ◇ c3 = LxPhase x t phase
  phase_t_eq_c1 : LxPhase x t phase ◇ t = c1

structure D4SSwapNewCycle
    (x c1 c2 c3 q s t : α)
    (first : D4LeftFirstReturn x c1 c2 c3 t 0) : Type u where
  u : α
  u_eq : u = t ◇ c3
  fresh : E677FreshOutsideSix x c1 c2 c3 q s u
  off_t_cycle : ∀ k, k < first.period → u ≠ LxPhase x t k
  firstReturn : D4LeftFirstReturn x c1 c2 c3 u 0
  u_t_eq_c1 : u ◇ t = c1

inductive D4SSwapCrossCycleReduction
    (x c1 c2 c3 q s t : α)
    (first : D4LeftFirstReturn x c1 c2 c3 t 0) : Prop
  | dual (h : D4SSwapDualCollision x c1 c2 c3 q s t)
  | positivePhase (h : D4SSwapPositivePhaseContact x c1 c2 c3 t first)
  | newCycle (h : D4SSwapNewCycle x c1 c2 c3 q s t first)

structure D4SSwapCommonRenewalPacket
    (x c1 c2 c3 q s : α) : Prop where
  q_s_right_c2_collision : q ◇ c2 = s ◇ c2
  qFixer_fixes_q : (q ◇ (q ◇ x)) ◇ q = q
  qFixer_fresh : E677FreshOutsideSix x c1 c2 c3 q s (q ◇ (q ◇ x))

structure D4SSwapCycleRenewalPacket
    (x c1 c2 c3 q s t : α)
    (first : D4LeftFirstReturn x c1 c2 c3 t 0) : Prop where
  basePacket : E677D4QDistinguishedPacket x c1 c2 c3
  traceStart : E677D4QSTaggedTraceStart x c1 c2 c3
  q_to_s : x ◇ q = s
  s_to_q : x ◇ s = q
  t_fresh : E677FreshOutsideSix x c1 c2 c3 q s t
  initial_trace : D4LeftTrace x c1 c2 c3 t 0
  bridge : t ◇ c2 = c3
  star : (t ◇ c3) ◇ t = c1
  common : D4SSwapCommonRenewalPacket x c1 c2 c3 q s
  reduction : D4SSwapCrossCycleReduction x c1 c2 c3 q s t first

inductive D4SSwapQFixerCycleTransition
    (x c1 c2 c3 q t p : α)
    (first : D4LeftFirstReturn x c1 c2 c3 t 0) : Prop
  | knownCycle
      (phase : Nat)
      (phase_lt : phase < first.period)
      (p_eq_phase : p = LxPhase x t phase)
      (phase_fixes_q : LxPhase x t phase ◇ q = q)
  | strictGrowth
      (off_t_cycle : ∀ k, k < first.period → p ≠ LxPhase x t k)
      (firstReturn : D4LeftFirstReturn x c1 c2 c3 p 0)
      (p_fixes_q : p ◇ q = q)

end FiniteMagmaE677.SSwap
end

namespace FiniteMagmaE677.SSwap
local infixl:65 " ◇ " => Magma'.op
section
universe u
variable {α : Type u} [Magma' α] [DecidableEq α]
/-- The six named points in the D4 S-swap branch. -/
def d4SSwapSixFinset
    (x c1 c2 c3 q s : α) : Finset α :=
  {x, c1, c2, c3, q, s}

/-- The phases with indices strictly below `period` in the left-`x` orbit of
`seed`. -/
def lxCycleFinset
    (x seed : α) (period : ℕ) : Finset α :=
  (Finset.range period).image (LxPhase x seed)

end

section
universe u
variable {alpha : Type u} [Magma' alpha]
/-- Algebraic data forced by one application of the explicit `q`-fixer. -/
structure D4SSwapQFixerPumpSeed
    (x c1 c2 c3 q s p u : alpha) : Prop where
  p_fixes_q : p ◇ q = q
  p_fresh : E677FreshOutsideSix x c1 c2 c3 q s p
  q_mul_u_eq_q : q ◇ u = q
  u_fresh : E677FreshOutsideSix x c1 c2 c3 q s u
  u_ne_p : u ≠ p
  u_not_fixes_q : u ◇ q ≠ q

/-- Exhaustive cycle contacts after adjoining `u = q ◇ p`. -/
inductive D4SSwapQFixerPumpTransition
    (x c1 c2 c3 q t p u : alpha)
    (first : D4LeftFirstReturn x c1 c2 c3 t 0) : Prop
  | bothOnT
      (pPhase uPhase : Nat)
      (pPhase_lt : pPhase < first.period)
      (uPhase_lt : uPhase < first.period)
      (p_eq : p = LxPhase x t pPhase)
      (u_eq : u = LxPhase x t uPhase)
      (pPhase_fixes_q : LxPhase x t pPhase ◇ q = q)
      (pPhase_ne_uPhase : pPhase ≠ uPhase)
  | pOnT_uEscape
      (pPhase : Nat)
      (pPhase_lt : pPhase < first.period)
      (p_eq : p = LxPhase x t pPhase)
      (pPhase_fixes_q : LxPhase x t pPhase ◇ q = q)
      (u_off_t : ∀ k, k < first.period → u ≠ LxPhase x t k)
      (uFirst : D4LeftFirstReturn x c1 c2 c3 u 0)
  | pNew_uOnT
      (p_off_t : ∀ k, k < first.period → p ≠ LxPhase x t k)
      (pFirst : D4LeftFirstReturn x c1 c2 c3 p 0)
      (uPhase : Nat)
      (uPhase_lt : uPhase < first.period)
      (u_eq : u = LxPhase x t uPhase)
  | pNew_uOnP
      (p_off_t : ∀ k, k < first.period → p ≠ LxPhase x t k)
      (pFirst : D4LeftFirstReturn x c1 c2 c3 p 0)
      (u_off_t : ∀ k, k < first.period → u ≠ LxPhase x t k)
      (uPhase : Nat)
      (uPhase_pos : 0 < uPhase)
      (uPhase_lt : uPhase < pFirst.period)
      (u_eq : u = LxPhase x p uPhase)
  | pNew_uEscape
      (p_off_t : ∀ k, k < first.period → p ≠ LxPhase x t k)
      (pFirst : D4LeftFirstReturn x c1 c2 c3 p 0)
      (u_off_t : ∀ k, k < first.period → u ≠ LxPhase x t k)
      (u_off_p : ∀ k, k < pFirst.period → u ≠ LxPhase x p k)
      (uFirst : D4LeftFirstReturn x c1 c2 c3 u 0)

/-- The retained input, canonical links, algebraic seed, and cycle classifier. -/
structure D4SSwapQFixerPumpPacket
    (x c1 c2 c3 q s t p u : alpha)
    (first : D4LeftFirstReturn x c1 c2 c3 t 0) : Prop where
  input : D4SSwapCycleRenewalPacket x c1 c2 c3 q s t first
  q_eq : q = c2 ◇ x
  s_eq : s = c3 ◇ q
  seed : D4SSwapQFixerPumpSeed x c1 c2 c3 q s p u
  transition : D4SSwapQFixerPumpTransition x c1 c2 c3 q t p u first

end

end FiniteMagmaE677.SSwap

section
/- Standalone source export: q-square refinement in the D4 S-swap branch.
   This fragment intentionally has no imports; prepend the shared SSwap core. -/

section
universe u

namespace FiniteMagmaE677.SSwap
local infixl:65 " ◇ " => Magma'.op

variable {alpha : Type u} [Magma' alpha]

structure D4SSwapQSquareSeed
    (x c1 c2 c3 q s p u : alpha) : Prop where
  factor : p = u ◇ (q ◇ q)
  fresh : E677FreshOutsideSix x c1 c2 c3 q s (q ◇ q)
  ne_p : q ◇ q ≠ p
  ne_u : q ◇ q ≠ u

inductive D4SSwapBothOnTQSquareReduction
    (x c1 c2 c3 q s t p u : alpha)
    (first : D4LeftFirstReturn x c1 c2 c3 t 0) : Prop
  | threePhase
      (j l m : Nat)
      (j_lt : j < first.period)
      (l_lt : l < first.period)
      (m_lt : m < first.period)
      (p_eq : p = LxPhase x t j)
      (u_eq : u = LxPhase x t l)
      (v_eq : q ◇ q = LxPhase x t m)
      (pairwise : j ≠ l ∧ j ≠ m ∧ l ≠ m)
      (phase_relation :
        LxPhase x t j = LxPhase x t l ◇ LxPhase x t m)
  | strictGrowth
      (fresh : E677FreshOutsideSix x c1 c2 c3 q s (q ◇ q))
      (off_t_cycle : ∀ m, m < first.period →
        q ◇ q ≠ LxPhase x t m)
      (firstReturn : D4LeftFirstReturn x c1 c2 c3 (q ◇ q) 0)

inductive D4SSwapQFixerPumpQSquareOutcome
    (x c1 c2 c3 q s t p u : alpha)
    (first : D4LeftFirstReturn x c1 c2 c3 t 0) : Prop
  | bothOnT
      (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
      (pPhase uPhase : Nat)
      (pPhase_lt : pPhase < first.period)
      (uPhase_lt : uPhase < first.period)
      (p_eq : p = LxPhase x t pPhase)
      (u_eq : u = LxPhase x t uPhase)
      (pPhase_fixes_q : LxPhase x t pPhase ◇ q = q)
      (pPhase_ne_uPhase : pPhase ≠ uPhase)
      (reduction : D4SSwapBothOnTQSquareReduction
        x c1 c2 c3 q s t p u first)
  | pOnT_uEscape
      (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
      (pPhase : Nat)
      (pPhase_lt : pPhase < first.period)
      (p_eq : p = LxPhase x t pPhase)
      (pPhase_fixes_q : LxPhase x t pPhase ◇ q = q)
      (u_off_t : ∀ k, k < first.period → u ≠ LxPhase x t k)
      (uFirst : D4LeftFirstReturn x c1 c2 c3 u 0)
  | pNew_uOnT
      (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
      (p_off_t : ∀ k, k < first.period → p ≠ LxPhase x t k)
      (pFirst : D4LeftFirstReturn x c1 c2 c3 p 0)
      (uPhase : Nat)
      (uPhase_lt : uPhase < first.period)
      (u_eq : u = LxPhase x t uPhase)
  | pNew_uOnP
      (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
      (p_off_t : ∀ k, k < first.period → p ≠ LxPhase x t k)
      (pFirst : D4LeftFirstReturn x c1 c2 c3 p 0)
      (u_off_t : ∀ k, k < first.period → u ≠ LxPhase x t k)
      (uPhase : Nat)
      (uPhase_pos : 0 < uPhase)
      (uPhase_lt : uPhase < pFirst.period)
      (u_eq : u = LxPhase x p uPhase)
  | pNew_uEscape
      (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
      (p_off_t : ∀ k, k < first.period → p ≠ LxPhase x t k)
      (pFirst : D4LeftFirstReturn x c1 c2 c3 p 0)
      (u_off_t : ∀ k, k < first.period → u ≠ LxPhase x t k)
      (u_off_p : ∀ k, k < pFirst.period → u ≠ LxPhase x p k)
      (uFirst : D4LeftFirstReturn x c1 c2 c3 u 0)

inductive D4SSwapPNewUOnTQSquareReduction
    (x c1 c2 c3 q s t p u : alpha)
    (first : D4LeftFirstReturn x c1 c2 c3 t 0)
    (pFirst : D4LeftFirstReturn x c1 c2 c3 p 0) : Prop
  | vOnT
      (l m : Nat)
      (l_lt : l < first.period)
      (m_lt : m < first.period)
      (u_eq : u = LxPhase x t l)
      (v_eq : q ◇ q = LxPhase x t m)
      (l_ne_m : l ≠ m)
      (phase_relation : p = LxPhase x t l ◇ LxPhase x t m)
  | vOnP
      (l m : Nat)
      (l_lt : l < first.period)
      (m_pos : 0 < m)
      (m_lt : m < pFirst.period)
      (u_eq : u = LxPhase x t l)
      (v_eq : q ◇ q = LxPhase x p m)
      (phase_relation : p = LxPhase x t l ◇ LxPhase x p m)
  | strictGrowth
      (fresh : E677FreshOutsideSix x c1 c2 c3 q s (q ◇ q))
      (off_t_cycle : ∀ m, m < first.period → q ◇ q ≠ LxPhase x t m)
      (off_p_cycle : ∀ m, m < pFirst.period → q ◇ q ≠ LxPhase x p m)
      (firstReturn : D4LeftFirstReturn x c1 c2 c3 (q ◇ q) 0)

/-- Classification of `q ◇ q` in the `pNew_uOnP` leaf.  This records contact
or strict growth only; it supplies no fixer, iteration, or closure. -/
inductive D4SSwapPNewUOnPQSquareReduction
    (x c1 c2 c3 q s t p u : alpha)
    (first : D4LeftFirstReturn x c1 c2 c3 t 0)
    (pFirst : D4LeftFirstReturn x c1 c2 c3 p 0) : Prop
  | vOnT
      (l m : Nat)
      (l_pos : 0 < l)
      (l_lt : l < pFirst.period)
      (m_lt : m < first.period)
      (u_eq : u = LxPhase x p l)
      (v_eq : q ◇ q = LxPhase x t m)
      (phase_relation : p = LxPhase x p l ◇ LxPhase x t m)
  | vOnP
      (l m : Nat)
      (l_pos : 0 < l)
      (l_lt : l < pFirst.period)
      (m_pos : 0 < m)
      (m_lt : m < pFirst.period)
      (u_eq : u = LxPhase x p l)
      (v_eq : q ◇ q = LxPhase x p m)
      (l_ne_m : l ≠ m)
      (phase_relation : p = LxPhase x p l ◇ LxPhase x p m)
  | strictGrowth
      (fresh : E677FreshOutsideSix x c1 c2 c3 q s (q ◇ q))
      (off_t_cycle : ∀ m, m < first.period → q ◇ q ≠ LxPhase x t m)
      (off_p_cycle : ∀ m, m < pFirst.period → q ◇ q ≠ LxPhase x p m)
      (firstReturn : D4LeftFirstReturn x c1 c2 c3 (q ◇ q) 0)

def d4SSwapPNewMarkedPhaseSlack [DecidableEq alpha]
    (x t p : alpha) (dt dp : Nat) (marks : Finset alpha) : Nat :=
  ((lxCycleFinset x t dt ∪ lxCycleFinset x p dp) \ marks).card

inductive D4SSwapQFixerPumpPNewQSquareOutcome
    (x c1 c2 c3 q s t p u : alpha)
    (first : D4LeftFirstReturn x c1 c2 c3 t 0) : Prop
  | bothOnT
      (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
      (pPhase uPhase : Nat)
      (pPhase_lt : pPhase < first.period)
      (uPhase_lt : uPhase < first.period)
      (p_eq : p = LxPhase x t pPhase)
      (u_eq : u = LxPhase x t uPhase)
      (pPhase_fixes_q : LxPhase x t pPhase ◇ q = q)
      (pPhase_ne_uPhase : pPhase ≠ uPhase)
      (reduction : D4SSwapBothOnTQSquareReduction
        x c1 c2 c3 q s t p u first)
  | pOnT_uEscape
      (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
      (pPhase : Nat)
      (pPhase_lt : pPhase < first.period)
      (p_eq : p = LxPhase x t pPhase)
      (pPhase_fixes_q : LxPhase x t pPhase ◇ q = q)
      (u_off_t : ∀ k, k < first.period → u ≠ LxPhase x t k)
      (uFirst : D4LeftFirstReturn x c1 c2 c3 u 0)
  | pNew_uOnT
      (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
      (p_off_t : ∀ k, k < first.period → p ≠ LxPhase x t k)
      (pFirst : D4LeftFirstReturn x c1 c2 c3 p 0)
      (uPhase : Nat)
      (uPhase_lt : uPhase < first.period)
      (u_eq : u = LxPhase x t uPhase)
      (reduction : D4SSwapPNewUOnTQSquareReduction
        x c1 c2 c3 q s t p u first pFirst)
  | pNew_uOnP
      (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
      (p_off_t : ∀ k, k < first.period → p ≠ LxPhase x t k)
      (pFirst : D4LeftFirstReturn x c1 c2 c3 p 0)
      (u_off_t : ∀ k, k < first.period → u ≠ LxPhase x t k)
      (uPhase : Nat)
      (uPhase_pos : 0 < uPhase)
      (uPhase_lt : uPhase < pFirst.period)
      (u_eq : u = LxPhase x p uPhase)
      (reduction : D4SSwapPNewUOnPQSquareReduction
        x c1 c2 c3 q s t p u first pFirst)
  | pNew_uEscape
      (pump : D4SSwapQFixerPumpPacket x c1 c2 c3 q s t p u first)
      (p_off_t : ∀ k, k < first.period → p ≠ LxPhase x t k)
      (pFirst : D4LeftFirstReturn x c1 c2 c3 p 0)
      (u_off_t : ∀ k, k < first.period → u ≠ LxPhase x t k)
      (u_off_p : ∀ k, k < pFirst.period → u ≠ LxPhase x p k)
      (uFirst : D4LeftFirstReturn x c1 c2 c3 u 0)

end FiniteMagmaE677.SSwap
end
end

section
namespace FiniteMagmaE677.SSwap
local infixl:65 " ◇ " => Magma'.op
universe u

abbrev CycleRenewal {α : Type u} (op : α → α → α)
    (x c1 c2 c3 q s t : α)
    (first : FirstReturn.D4FirstReturn op x c1 c2 c3 t 0) : Prop :=
  @D4SSwapCycleRenewalPacket α ⟨op⟩ x c1 c2 c3 q s t first

abbrev Pump {α : Type u} (op : α → α → α)
    (x c1 c2 c3 q s t p u : α)
    (first : FirstReturn.D4FirstReturn op x c1 c2 c3 t 0) : Prop :=
  @D4SSwapQFixerPumpPacket α ⟨op⟩ x c1 c2 c3 q s t p u first

abbrev QSquareOutcome {α : Type u} (op : α → α → α)
    (x c1 c2 c3 q s t p u : α)
    (first : FirstReturn.D4FirstReturn op x c1 c2 c3 t 0) : Prop :=
  @D4SSwapQFixerPumpPNewQSquareOutcome α ⟨op⟩ x c1 c2 c3 q s t p u first

abbrev QSquareSeed {α : Type u} (op : α → α → α)
    (x c1 c2 c3 q s p u : α) : Prop :=
  @D4SSwapQSquareSeed α ⟨op⟩ x c1 c2 c3 q s p u

abbrev cyclePoints {α : Type u} [DecidableEq α] (op : α → α → α)
    (x seed : α) (period : ℕ) : Finset α :=
  letI : Magma' α := ⟨op⟩
  lxCycleFinset x seed period

abbrev namedSix {α : Type u} [DecidableEq α]
    (x c1 c2 c3 q s : α) : Finset α := {x, c1, c2, c3, q, s}

abbrev markedSlack {α : Type u} [DecidableEq α] (op : α → α → α)
    (x t p : α) (dt dp : ℕ) (marks : Finset α) : ℕ :=
  letI : Magma' α := ⟨op⟩
  d4SSwapPNewMarkedPhaseSlack x t p dt dp marks

end FiniteMagmaE677.SSwap
end


