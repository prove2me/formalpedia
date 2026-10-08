-- Prove2me | Definitions.Def_SingleMachinePrec_IntervalChromatic_IncomparableGraph
-- name    : SingleMachinePrec_IntervalChromatic_IncomparableGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:11:55.495797+00:00
-- url     : https://prove2.me/theorems/3e05e532-8045-408d-989f-5e363f63b431
-- title:
--   The graph of ordered incomparable pairs
-- statement:
--   Let $P$ be a partial order on a set $N$. An **ordered incomparable pair** is $(x,y)$ such that neither $x\le_P y$ nor $y\le_P x$. A **linear extension** is a linear order $L$ on $N$ containing $P$, and it reverses $(x,y)$ when $y\le_L x$.
--
--   The graph $G_P$ has the ordered incomparable pairs as vertices. Distinct vertices $u,v$ are adjacent precisely when each can be reversed individually by some linear extension, but no one linear extension reverses both:
--
--   $$
--   u\sim_{G_P}v\iff u\ne v\ \land\ (\exists L_u\supseteq P:\ L_u\text{ reverses }u)\ \land\ (\exists L_v\supseteq P:\ L_v\text{ reverses }v)\ \land\ \neg\exists L\supseteq P:\ L\text{ reverses both }u,v.
--   $$
--
--   This is the two-vertex part of the paper's hypergraph of minimal non-simultaneously reversible sets. The singleton clauses express that minimality explicitly.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 655, §2.1 and p. 656, §3; DOI 10.1287/moor.1110.0512

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_Poset

namespace SingleMachinePrec.IntervalChromatic

def IncomparablePair {N : Type*} (P : N → N → Prop) : Type _ :=
  {p : N × N // SingleMachinePrec.Framework.Incomparable P p.1 p.2}

/-- A reflexive linear extension of the precedence relation. -/
def LinearExtension {N : Type*} (P L : N → N → Prop) : Prop :=
  IsLinearOrder N L ∧ ∀ x y, P x y → L x y

/-- Reversing `(x,y)` means placing `y` before `x`. -/
def Reverses {N : Type*} (L : N → N → Prop) (p : N × N) : Prop :=
  L p.2 p.1

def Reversible {N : Type*} (P : N → N → Prop)
    (p : IncomparablePair P) : Prop :=
  ∃ L : N → N → Prop, LinearExtension P L ∧ Reverses L p.1

/-- The size-two minimal edges in the incomparable-pairs hypergraph. -/
def G {N : Type*} (P : N → N → Prop)
    (u v : IncomparablePair P) : Prop :=
  u ≠ v ∧ Reversible P u ∧ Reversible P v ∧
    ¬ ∃ L : N → N → Prop,
      LinearExtension P L ∧ Reverses L u.1 ∧ Reverses L v.1

end SingleMachinePrec.IntervalChromatic


