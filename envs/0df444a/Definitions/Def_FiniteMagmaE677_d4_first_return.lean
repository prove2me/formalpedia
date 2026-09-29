-- Prove2me | Definitions.Def_FiniteMagmaE677_d4_first_return
-- name    : FiniteMagmaE677_d4_first_return
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-23T20:37:55.537961+00:00
-- url     : https://prove2.me/theorems/f34a90cc-72a8-4e27-bcda-4d9aa15e296e
-- title:
--   Tagged period-four traces and exact first-return cycles
-- statement:
--   This interface records exact finite return cycles for the five source branches of a period-four E677 collision.
--
--   For $L_x(z)=x\diamond z$, a trace records pairwise distinct iterates of a seed, all outside the displayed four-element base cycle. A first-return packet records a positive period equal to the seed's minimal period, a specified initialized depth smaller than that period, the return equation, and the entire simple trace up to the last point before return.
--
--   The distinguished packet retains the four-cycle equations, all six pairwise inequalities between its base points, and the q-collision equations and freshness. Separate R and S starts retain their source equations. Initialization and first-return packets have five constructors: R through one or two steps, S through one or two steps, and the swapped-S seed. The swapped-S constructor retains its cross-cycle bridge.
--
--   These are definitions of the data used by the first-return theorem and its open branch closeouts. They assert neither the existence of a fixer nor the impossibility of any branch.
-- source:
--   Adam McKenna, The Missing Pair, revision 9b76827c2246f0e6288466768f15b5c6f9350d71; Piece1D4FirstReturn.lean, e677_minimalPeriodFour_orbitRightCollision_hasFixer_or_firstReturnPacket; trace ingress in Piece1D4TaggedTraceStart.lean and Piece1D4TraceInitialization.lean. https://github.com/flound1129/the-missing-pair/blob/9b76827c2246f0e6288466768f15b5c6f9350d71/lean/E677/Spine/Piece1D4FirstReturn.lean

import Mathlib.Dynamics.PeriodicPts.Lemmas
import Definitions.Def_FiniteMagmaE677

/-!
# Standalone D4 first-return reduction

This file is the small Prove2Me boundary for the proved finite first-return
step.  The algebraic D4 dispatcher may supply `D4Initialization`; this file
does not import the internal E677 spine.  The five branch constructors retain
the R/S tags, displayed equations, freshness witness, exact return period, and
the disjoint orbit trace.
-/

namespace FiniteMagmaE677.FirstReturn

universe u

def orbitPoint {α : Type u} (op : α → α → α) (x : α) (k : ℕ) (seed : α) : α :=
  (op x)^[k] seed

def FreshOutsideSix {α : Type u} (x c1 c2 c3 q s t : α) : Prop :=
  t ≠ x ∧ t ≠ c1 ∧ t ≠ c2 ∧ t ≠ c3 ∧ t ≠ q ∧ t ≠ s

structure D4Trace {α : Type u} (op : α → α → α)
    (x c1 c2 c3 seed : α) (n : ℕ) : Prop where
  outside : ∀ i, i ≤ n →
    orbitPoint op x i seed ≠ x ∧
      orbitPoint op x i seed ≠ c1 ∧
      orbitPoint op x i seed ≠ c2 ∧
      orbitPoint op x i seed ≠ c3
  index_injective : ∀ i, i ≤ n → ∀ j, j ≤ n →
    orbitPoint op x i seed = orbitPoint op x j seed → i = j

structure D4FirstReturn {α : Type u} (op : α → α → α)
    (x c1 c2 c3 seed : α) (n : ℕ) : Type where
  period : ℕ
  period_pos : 0 < period
  period_eq_minimalPeriod :
    period = Function.minimalPeriod (fun z : α ↦ op x z) seed
  initial_lt_period : n < period
  returns : orbitPoint op x period seed = seed
  simple_prefix : D4Trace op x c1 c2 c3 seed (period - 1)

structure D4Distinguished {α : Type u} (op : α → α → α)
    (x c1 c2 c3 : α) : Prop where
  orbit_c1 : op x x = c1
  orbit_c2 : op x c1 = c2
  orbit_c3 : op x c2 = c3
  orbit_closes : op x c3 = x
  x_ne_c1 : x ≠ c1
  x_ne_c2 : x ≠ c2
  x_ne_c3 : x ≠ c3
  c1_ne_c2 : c1 ≠ c2
  c1_ne_c3 : c1 ≠ c3
  c2_ne_c3 : c2 ≠ c3
  q_collision : op c2 x = op c3 x
  q_packet_preimage : op c1 (op c2 x) = x
  q_packet_return : op c2 (op c2 x) = c1
  q_ne_x : op c2 x ≠ x
  q_ne_c1 : op c2 x ≠ c1
  q_ne_c2 : op c2 x ≠ c2
  q_ne_c3 : op c2 x ≠ c3

structure RTaggedStart {α : Type u} (op : α → α → α)
    (x c1 c2 c3 : α) : Prop where
  r_ne_x : op c1 c2 ≠ x
  r_ne_c1 : op c1 c2 ≠ c1
  r_ne_c2 : op c1 c2 ≠ c2
  r_ne_c3 : op c1 c2 ≠ c3
  r_ne_q : op c1 c2 ≠ op c2 x
  trace_start :
    FreshOutsideSix x c1 c2 c3 (op c2 x) (op c1 c2) (op x (op c2 x)) ∨
      (op x (op c2 x) = op c1 c2 ∧
        FreshOutsideSix x c1 c2 c3 (op c2 x) (op c1 c2) (op x (op c1 c2)))

structure STaggedStart {α : Type u} (op : α → α → α)
    (x c1 c2 c3 : α) : Prop where
  r_eq_c1 : op c1 c2 = c1
  s_ne_x : op c3 (op c2 x) ≠ x
  s_ne_c1 : op c3 (op c2 x) ≠ c1
  s_ne_c2 : op c3 (op c2 x) ≠ c2
  s_ne_c3 : op c3 (op c2 x) ≠ c3
  s_ne_q : op c3 (op c2 x) ≠ op c2 x
  trace_start :
    FreshOutsideSix x c1 c2 c3 (op c2 x) (op c3 (op c2 x)) (op x (op c2 x)) ∨
      (op x (op c2 x) = op c3 (op c2 x) ∧
        FreshOutsideSix x c1 c2 c3 (op c2 x) (op c3 (op c2 x))
          (op x (op c3 (op c2 x)))) ∨
      (op x (op c2 x) = op c3 (op c2 x) ∧
        op x (op c3 (op c2 x)) = op c2 x ∧
        FreshOutsideSix x c1 c2 c3 (op c2 x) (op c3 (op c2 x))
          (op c2 (op c3 (op c2 x))) ∧
        op (op c2 (op c3 (op c2 x))) c2 = c3)

inductive D4InitializationBranch {α : Type u} (op : α → α → α)
    (x c1 c2 c3 : α) : Type
  | rSeedQThroughOne (start : RTaggedStart op x c1 c2 c3)
      (fresh : FreshOutsideSix x c1 c2 c3 (op c2 x) (op c1 c2) (op x (op c2 x)))
      (trace : D4Trace op x c1 c2 c3 (op c2 x) 1) :
      D4InitializationBranch op x c1 c2 c3
  | rSeedQThroughTwo (start : RTaggedStart op x c1 c2 c3)
      (q_to_r : op x (op c2 x) = op c1 c2)
      (fresh : FreshOutsideSix x c1 c2 c3 (op c2 x) (op c1 c2) (op x (op c1 c2)))
      (trace : D4Trace op x c1 c2 c3 (op c2 x) 2) :
      D4InitializationBranch op x c1 c2 c3
  | sSeedQThroughOne (start : STaggedStart op x c1 c2 c3)
      (fresh : FreshOutsideSix x c1 c2 c3 (op c2 x) (op c3 (op c2 x)) (op x (op c2 x)))
      (trace : D4Trace op x c1 c2 c3 (op c2 x) 1) :
      D4InitializationBranch op x c1 c2 c3
  | sSeedQThroughTwo (start : STaggedStart op x c1 c2 c3)
      (q_to_s : op x (op c2 x) = op c3 (op c2 x))
      (fresh : FreshOutsideSix x c1 c2 c3 (op c2 x) (op c3 (op c2 x))
        (op x (op c3 (op c2 x))))
      (trace : D4Trace op x c1 c2 c3 (op c2 x) 2) :
      D4InitializationBranch op x c1 c2 c3
  | sSwapSeedT (start : STaggedStart op x c1 c2 c3)
      (q_to_s : op x (op c2 x) = op c3 (op c2 x))
      (s_to_q : op x (op c3 (op c2 x)) = op c2 x)
      (fresh : FreshOutsideSix x c1 c2 c3 (op c2 x) (op c3 (op c2 x))
        (op c2 (op c3 (op c2 x))))
      (trace : D4Trace op x c1 c2 c3 (op c2 (op c3 (op c2 x))) 0)
      (bridge : op (op c2 (op c3 (op c2 x))) c2 = c3) :
      D4InitializationBranch op x c1 c2 c3

structure D4Initialization {α : Type u} (op : α → α → α)
    (x c1 c2 c3 : α) : Type where
  distinguished : D4Distinguished op x c1 c2 c3
  branch : D4InitializationBranch op x c1 c2 c3

inductive D4FirstReturnBranch {α : Type u} (op : α → α → α)
    (x c1 c2 c3 : α) : Type
  | rSeedQThroughOne (start : RTaggedStart op x c1 c2 c3)
      (fresh : FreshOutsideSix x c1 c2 c3 (op c2 x) (op c1 c2) (op x (op c2 x)))
      (initial_trace : D4Trace op x c1 c2 c3 (op c2 x) 1)
      (first_return : D4FirstReturn op x c1 c2 c3 (op c2 x) 1)
  | rSeedQThroughTwo (start : RTaggedStart op x c1 c2 c3)
      (q_to_r : op x (op c2 x) = op c1 c2)
      (fresh : FreshOutsideSix x c1 c2 c3 (op c2 x) (op c1 c2) (op x (op c1 c2)))
      (initial_trace : D4Trace op x c1 c2 c3 (op c2 x) 2)
      (first_return : D4FirstReturn op x c1 c2 c3 (op c2 x) 2)
  | sSeedQThroughOne (start : STaggedStart op x c1 c2 c3)
      (fresh : FreshOutsideSix x c1 c2 c3 (op c2 x) (op c3 (op c2 x)) (op x (op c2 x)))
      (initial_trace : D4Trace op x c1 c2 c3 (op c2 x) 1)
      (first_return : D4FirstReturn op x c1 c2 c3 (op c2 x) 1)
  | sSeedQThroughTwo (start : STaggedStart op x c1 c2 c3)
      (q_to_s : op x (op c2 x) = op c3 (op c2 x))
      (fresh : FreshOutsideSix x c1 c2 c3 (op c2 x) (op c3 (op c2 x))
        (op x (op c3 (op c2 x))))
      (initial_trace : D4Trace op x c1 c2 c3 (op c2 x) 2)
      (first_return : D4FirstReturn op x c1 c2 c3 (op c2 x) 2)
  | sSwapSeedT (start : STaggedStart op x c1 c2 c3)
      (q_to_s : op x (op c2 x) = op c3 (op c2 x))
      (s_to_q : op x (op c3 (op c2 x)) = op c2 x)
      (fresh : FreshOutsideSix x c1 c2 c3 (op c2 x) (op c3 (op c2 x))
        (op c2 (op c3 (op c2 x))))
      (initial_trace : D4Trace op x c1 c2 c3 (op c2 (op c3 (op c2 x))) 0)
      (first_return : D4FirstReturn op x c1 c2 c3 (op c2 (op c3 (op c2 x))) 0)
      (bridge : op (op c2 (op c3 (op c2 x))) c2 = c3)

structure D4FirstReturnPacket {α : Type u} (op : α → α → α)
    (x c1 c2 c3 : α) : Type where
  distinguished : D4Distinguished op x c1 c2 c3
  branch : D4FirstReturnBranch op x c1 c2 c3

end FiniteMagmaE677.FirstReturn


