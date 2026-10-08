-- Prove2me | Definitions.Def_InteractiveConsistency_Impossibility_Construction
-- name    : InteractiveConsistency_Impossibility_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:50.683996+00:00
-- url     : https://prove2.me/theorems/41a61806-a80d-4c67-a6e6-b1563710d829
-- title:
--   Section 4, proof of the THEOREM (p. 232) — the scenarios α, β, σ defined recursively by (i)–(iii)
-- statement:
--   Let $A, B, C$ be pairwise disjoint sets with $A\cup B\cup C = P$, and let $v, v'\in V$. In the clauses below, $a$, $b$, $c$, $p$ range independently over $A$, $B$, $C$, $P$. The scenarios $\alpha$, $\beta$, $\sigma : P^+\to V$ are defined by recursion on the length of the string:
--
--   (i) For every $w\in P^+$ not ending in a member of $C$,
--   $$\alpha(w)=\beta(w)=\sigma(w)=v.$$
--
--   (ii) For strings of length one or two ending in $c\in C$,
--   $$\alpha(c)=\alpha(ac)=\alpha(bc)=\alpha(cc)=v,\quad \beta(c)=\beta(ac)=\beta(bc)=\beta(cc)=v',$$
--   $$\sigma(c)=\sigma(ac)=\sigma(cc)=v,\qquad \sigma(bc)=v'.$$
--
--   (iii) For every nonempty $w\in P^*$ ending in a member of $C$,
--   $$\alpha(paw)=\alpha(aw),\quad \alpha(pbw)=\beta(bw),\quad \alpha(pcw)=\alpha(cw),$$
--   $$\beta(paw)=\alpha(aw),\quad \beta(pbw)=\beta(bw),\quad \beta(pcw)=\beta(cw),$$
--   $$\sigma(paw)=\sigma(aw),\quad \sigma(pbw)=\sigma(bw),\quad \sigma(acw)=\alpha(cw),\quad \sigma(bcw)=\beta(cw).$$
--
--   In $\alpha$ the processors of $C$ have private value $v$, in $\beta$ they have $v'$; in $\alpha$ the processors of $B$ lie by relaying what they would relay in $\beta$, in $\beta$ those of $A$ relay as in $\alpha$, and in $\sigma$ the processors of $C$ tell $A$ what they would say in $\alpha$ and tell $B$ what they would say in $\beta$. These are the three scenarios of the impossibility proof.
--
--   **Formalization Note** The page leaves $\sigma(c'cw)$, $c, c'\in C$, $w$ nonempty, unspecified; it is set to $\sigma(cw)$ here (no statement depends on this value). The letters $a, b, c$ in "$cc$", "$acw$", … range over $A$, $B$, $C$ independently, so $\alpha(c'c)=v$ for all $c, c'\in C$. The scenarios are total functions on lists: the empty list and lists with a letter outside $P$ get $v$ in all three. The page's $w\in P^*c$ in (iii) is written as a nonempty list whose last letter lies in $C$, after the prefix $p\,a$ (resp. $p\,b$, $p\,c$).
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), p. 232, Section 4, proof of the THEOREM, definitions (i)–(iii)

import Mathlib
import Definitions.Def_InteractiveConsistency_Impossibility_Scenario

namespace InteractiveConsistency.Impossibility

/-- The three scenarios `α`, `β`, `σ` of the proof of the THEOREM (p. 232). -/
inductive Which
  | alpha
  | beta
  | sigma
  deriving DecidableEq

/-- `true` iff the string `s` is nonempty and its last letter (the originator) lies in `C`. -/
def lastIn {α : Type*} [DecidableEq α] (C : Finset α) (s : List α) : Bool :=
  s.getLast?.any (fun c => decide (c ∈ C))

/-- The recursion (i)–(iii) of p. 232, on nonempty strings, for a partition `A, B, C` of `P` and
values `v, v'`. Each letter `a`, `b`, `c` of the page ranges over `A`, `B`, `C` independently.

* (i) a string not ending in a member of `C` gets `v` in all three scenarios;
* (ii) strings of length one or two ending in `c ∈ C`:
  `α(c) = α(ac) = α(bc) = α(cc) = v`, `β(c) = β(ac) = β(bc) = β(cc) = v'`,
  `σ(c) = σ(ac) = σ(cc) = v`, `σ(bc) = v'`;
* (iii) for `p ∈ P` and `w` ending in a member of `C` (here `y :: z :: w` has length at least two):
  `α(paw) = α(aw)`, `α(pbw) = β(bw)`, `α(pcw) = α(cw)`;
  `β(paw) = α(aw)`, `β(pbw) = β(bw)`, `β(pcw) = β(cw)`;
  `σ(paw) = σ(aw)`, `σ(pbw) = σ(bw)`, `σ(acw) = α(cw)`, `σ(bcw) = β(cw)`.

The page leaves `σ(c'cw)` (`c, c' ∈ C`, `w ≠` empty) unspecified; it is set here to `σ(cw)`.
The empty string, which is not in `P⁺`, gets `v`. -/
def core {α V : Type*} [DecidableEq α] (A B C : Finset α) (v v' : V) : Which → List α → V
  | _, [] => v
  | .alpha, [_] => v
  | .beta, [x] => if x ∈ C then v' else v
  | .sigma, [_] => v
  | .alpha, [_, _] => v
  | .beta, [_, y] => if y ∈ C then v' else v
  | .sigma, [x, y] => if y ∈ C then (if x ∈ B then v' else v) else v
  | .alpha, _ :: y :: z :: w =>
      if lastIn C (z :: w) then
        (if y ∈ B then core A B C v v' .beta (y :: z :: w)
          else core A B C v v' .alpha (y :: z :: w))
      else v
  | .beta, _ :: y :: z :: w =>
      if lastIn C (z :: w) then
        (if y ∈ A then core A B C v v' .alpha (y :: z :: w)
          else core A B C v v' .beta (y :: z :: w))
      else v
  | .sigma, p :: y :: z :: w =>
      if lastIn C (z :: w) then
        (if y ∈ C then
          (if p ∈ A then core A B C v v' .alpha (y :: z :: w)
            else if p ∈ B then core A B C v v' .beta (y :: z :: w)
            else core A B C v v' .sigma (y :: z :: w))
          else core A B C v v' .sigma (y :: z :: w))
      else v

/-- The scenario `k ∈ {α, β, σ}` of p. 232 as a total function on `List α`: on strings over `P`
it is given by the recursion `core`; on strings with a letter outside `P` (which are not in `P⁺`
and are never constrained) all three scenarios take the same value `v`. -/
def scen {α V : Type*} [DecidableEq α] (P A B C : Finset α) (v v' : V) (k : Which)
    (s : List α) : V :=
  if IsString P s then core A B C v v' k s else v

/-- The scenario `α` of p. 232. -/
abbrev alphaScen {α V : Type*} [DecidableEq α] (P A B C : Finset α) (v v' : V) : List α → V :=
  scen P A B C v v' .alpha

/-- The scenario `β` of p. 232. -/
abbrev betaScen {α V : Type*} [DecidableEq α] (P A B C : Finset α) (v v' : V) : List α → V :=
  scen P A B C v v' .beta

/-- The scenario `σ` of p. 232. -/
abbrev sigmaScen {α V : Type*} [DecidableEq α] (P A B C : Finset α) (v v' : V) : List α → V :=
  scen P A B C v v' .sigma

end InteractiveConsistency.Impossibility


