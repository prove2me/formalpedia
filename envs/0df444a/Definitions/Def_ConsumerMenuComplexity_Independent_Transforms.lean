-- Prove2me | Definitions.Def_ConsumerMenuComplexity_Independent_Transforms
-- name    : ConsumerMenuComplexity_Independent_Transforms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:02:18.642988+00:00
-- url     : https://prove2.me/theorems/15387983-09ce-4567-bff4-770e5dd0668c
-- title:
--   §5.1 — same-price projection and the actual free-lottery replacement
-- statement:
--   Let $S$ be a menu and $M$ its selected mechanism. Its projection is the set of both triples $(q_1,0,p)$ and $(0,q_2,p)$ for every $(q_1,q_2,p)\in S$. The selected projected mechanism compares the original choices at $(v_1,0)$ and $(0,v_2)$, zeros the other allocation coordinate at the same price, and selects the choice with larger axis utility, preferring item 1 when those utilities tie.
--
--   For a single-item menu put $d=u^M(0,1)$. Its free replacement keeps exactly the original options with $q_2=0$ and adds $(0,d,0)$:
--   $$S^{\rm free}=\{(q_1,0,p)\in S\}\cup\{(0,d,0)\}.$$
--   The complete selection rule keeps the original selected item-1 option whenever it gives the item-1 axis utility and remains at least as good as the new fallback. Otherwise it compares that axis utility with $dv_2$, taking the original item-1 axis option under strict preference and the free lottery in the remaining case. Thus existing item-1 ties retain their original selected lottery, and original item-2 ties select the free lottery. The rule also specifies reports with $v_2>1$ and the edge $d=0$.
--
--   These are transformations computed from the original menu and mechanism. Their validity, utility identities, objective comparisons and supply comparisons are theorem obligations, rather than assumptions in these definitions.
-- source:
--   Goldner, Mohan and Phung, On the Menu Complexity of Consumer Utility Maximization, November 3, 2026 preprint, STOC 2027 submission #10, SHA-256 4baa3f39e319dd0a0dd217840839edadc0a463c80f799a7858fa61ddc5de9cb4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/10.pdf, §5.1.2–5.1.3, PDF pp.17–19 (printed pp.16–18), Lemmas 5.2–5.4

import Mathlib
import Definitions.Def_ConsumerMenuComplexity_Independent_Mechanisms

namespace ConsumerMenuComplexity.Independent

def projectMenu (S : Set Option) : Set Option :=
  {o | ∃ a ∈ S, o = option (a.1 0) 0 a.2 ∨ o = option 0 (a.1 1) a.2}

/-- Select the better original axis option, preferring item 1 in an axis tie. -/
noncomputable def projectedChoice (M : Mechanism) (v : TypeSpace) : Option :=
  let a := typeAt (v 0) 0
  let b := typeAt 0 (v 1)
  if utility M b ≤ utility M a then option (M.q a 0) 0 (M.s a)
  else option 0 (M.q b 1) (M.s b)

noncomputable def projected (M : Mechanism) : Mechanism where
  q v := (projectedChoice M v).1
  s v := (projectedChoice M v).2

def freeProbability (M : Mechanism) : ℝ := utility M (typeAt 0 1)

def freeMenu (S : Set Option) (M : Mechanism) : Set Option :=
  {o ∈ S | o.1 1 = 0} ∪ {option 0 (freeProbability M) 0}

/-- Keep a chosen item-1 option if it remains maximal. Otherwise compare the original
axis choice with the new free lottery. This includes every endpoint and d=0. -/
noncomputable def freeChoice (M : Mechanism) (v : TypeSpace) : Option :=
  let a := typeAt (v 0) 0
  let u₁ := utility M a
  let fallback := freeProbability M * (v 1 : ℝ)
  if M.q v 1 = 0 ∧ utility M v = u₁ ∧ fallback ≤ u₁ then selected M v
  else if fallback < u₁ then option (M.q a 0) 0 (M.s a)
  else option 0 (freeProbability M) 0

noncomputable def madeFree (M : Mechanism) : Mechanism where
  q v := (freeChoice M v).1
  s v := (freeChoice M v).2

end ConsumerMenuComplexity.Independent


