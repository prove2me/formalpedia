-- Prove2me | Definitions.Def_PooledTestingAdaptivity_Gap_ReducedTree
-- name    : PooledTestingAdaptivity_Gap_ReducedTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:23:26.057934+00:00
-- url     : https://prove2.me/theorems/fc179f24-b27e-44a4-9d4a-85be1f2cad21
-- title:
--   Reduced query–offer trees, stopping indicators and failure probabilities
-- statement:
--   Let $E$ be any finite coordinate set, possibly empty. A reduced tree has leaves, binary queries labelled $A\subseteq E$, and offers labelled $S\subseteq E$ with one continuation. A query follows its zero child when $z_A=0$ and its positive child otherwise. All labels below a query's zero child must avoid $A$. An offer stops when $z_S=0$ and otherwise continues. Offers impose no extra descendant-disjointness condition; empty labels are permitted.
--
--   Here $z_j=1$ means infected in the virtual profile and healthy in its companion. Each encountered offer has an independent trial, whose result does not affect traversal, with success probability
--
--   $$p_S(z)=2^{-1-|\{j\in S:z_j=0\}|}.$$
--
--   The factor $1/2$ retains the implicit healthy focal person. Write $I_T(z)$ for the indicator of stopping at an offer and $O_T(z)$ for the list of encountered offers, including the stopping one. The exact failure probability is
--
--   $$F_T(z)=\prod_{S\text{ occurrence in }O_T(z)}(1-p_S(z)).$$
--
--   Repeated offers contribute separate factors; an empty product is one. An increasing set $R$ is closed under coordinatewise increases in $z$. Definitions 3.4 and 4.3 are represented by this single shared definition.
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), Definitions 3.4 and 4.3, Eqs. (4)–(5) and (11)–(12), printed pp. 7, 13–14, PDF pp. 8, 14–15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1397.pdf

import Mathlib

namespace PooledTestingAdaptivity.Gap

/-- Definitions 3.4 and 4.3: the same query-offer tree, with possibly empty labels. -/
inductive ReducedTree (E : Type) where
  | leaf : ReducedTree E
  | query (A : Finset E) (zero positive : ReducedTree E) : ReducedTree E
  | offer (S : Finset E) (continuation : ReducedTree E) : ReducedTree E

def ReducedTree.avoids {E : Type} [DecidableEq E] (A : Finset E) : ReducedTree E → Prop
  | .leaf => True
  | .query S zero pos => Disjoint S A ∧ zero.avoids A ∧ pos.avoids A
  | .offer S next => Disjoint S A ∧ next.avoids A

/-- Only queries impose descendant disjointness; offers impose no such condition. -/
def ReducedTree.Normalized {E : Type} [DecidableEq E] : ReducedTree E → Prop
  | .leaf => True
  | .query A zero pos => zero.avoids A ∧ zero.Normalized ∧ pos.Normalized
  | .offer _ next => next.Normalized

/-- Auxiliary bits mean infected in the virtual profile, healthy in the companion. -/
def zeroOn {E : Type} (S : Finset E) (z : E → Bool) : Bool :=
  decide (∀ j ∈ S, z j = false)

/-- All encountered offers, including the stopping one, with multiplicities. -/
def ReducedTree.offers {E : Type} (z : E → Bool) : ReducedTree E → List (Finset E)
  | .leaf => []
  | .query A zero pos => if zeroOn A z then zero.offers z else pos.offers z
  | .offer S next => S :: (if zeroOn S z then [] else next.offers z)

def ReducedTree.stops {E : Type} (z : E → Bool) : ReducedTree E → Bool
  | .leaf => false
  | .query A zero pos => if zeroOn A z then zero.stops z else pos.stops z
  | .offer S next => if zeroOn S z then true else next.stops z

/-- The healthy focal person is implicit; evaluation-infected companions have z_j=false. -/
noncomputable def offerSuccess {E : Type} (S : Finset E) (z : E → Bool) : ℝ :=
  (2 : ℝ)⁻¹ ^ (1 + (S.filter fun j => z j = false).card)

noncomputable def ReducedTree.failure {E : Type} (T : ReducedTree E) (z : E → Bool) : ℝ :=
  ((T.offers z).map fun S => 1 - offerSuccess S z).prod

def ReducedTree.stopIndicator {E : Type} (T : ReducedTree E) (z : E → Bool) : ℝ :=
  if T.stops z then 1 else 0

/-- All increasing subsets, including the empty set and the full cube. -/
def Increasing {E : Type} (R : Finset (E → Bool)) : Prop :=
  ∀ z ∈ R, ∀ z', (∀ j, z j ≤ z' j) → z' ∈ R

end PooledTestingAdaptivity.Gap


