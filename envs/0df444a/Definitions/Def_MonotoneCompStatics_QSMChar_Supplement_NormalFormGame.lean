-- Prove2me | Definitions.Def_MonotoneCompStatics_QSMChar_Supplement_NormalFormGame
-- name    : MonotoneCompStatics_QSMChar_Supplement_NormalFormGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:06:41.040982+00:00
-- url     : https://prove2.me/theorems/30f9471b-4455-4267-a4f7-d5378aea41c9
-- title:
--   Arbitrary pure normal-form games and Nash equilibrium
-- statement:
--   Let $I$ be a player set and $S_i$ an arbitrary pure action type for each player. A normal-form game has payoffs $\pi_i(a,x_{-i})\in\mathbb R$ on the own action and the full tuple of opponent actions. Its Nash profiles are
--   $$E=\{x:\ \forall i\ \forall a\in S_i,\ \pi_i(a,x_{-i})\le\pi_i(x_i,x_{-i})\}.$$
--   This general object contains no order, finiteness or continuity assumptions; the ordinal strategic-complementarity refinement supplies those stated in the source. Opponent profiles omit the own coordinate rather than carrying a redundant own action.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), DOI 10.2307/2951479, p.175, PDF 20, game setting

import Mathlib

namespace MonotoneCompStatics.QSMChar.Supplement

/-- An arbitrary pure normal-form game, before imposing any order or topology. -/
structure NormalFormGame (I : Type*) (S : I → Type*) where
  payoff : (i : I) → S i → ((j : {j : I // j ≠ i}) → S j.val) → ℝ

def opponents {I : Type*} {S : I → Type*} (x : (i : I) → S i) (i : I) :
    (j : {j : I // j ≠ i}) → S j.val := fun j => x j.val

def Nash {I : Type*} {S : I → Type*} (G : NormalFormGame I S)
    (x : (i : I) → S i) : Prop :=
  ∀ i (a : S i), G.payoff i a (opponents x i) ≤ G.payoff i (x i) (opponents x i)

end MonotoneCompStatics.QSMChar.Supplement


