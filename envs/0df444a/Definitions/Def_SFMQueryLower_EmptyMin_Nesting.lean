-- Prove2me | Definitions.Def_SFMQueryLower_EmptyMin_Nesting
-- name    : SFMQueryLower_EmptyMin_Nesting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:21:07.654621+00:00
-- url     : https://prove2.me/theorems/d6059c25-3386-4013-825f-f429204b2a26
-- title:
--   The single-layer nesting operation
-- statement:
--   Let $V$ be an $n$-element set, let $P,R\subseteq V$, let $w$ be a natural number, and let $g$ be real-valued on subsets of $V\setminus(P\cup R)$. Define
--   $$h(S)=\begin{cases}w|V||V\setminus S|&S\cap R\ne\varnothing,\\ w|S|&S\cap R=\varnothing,\ P\nsubseteq S,\\ g(S\setminus P)&S\cap R=\varnothing,\ P\subseteq S.\end{cases}$$
--   The recursive branch restricts its argument to the actual inner ground set. Lemma 2.1 states the submodularity and range guarantees under its nonempty disjoint-block and bounded-inner-function hypotheses. This operation supplies the construction's shared single-layer interface.
--
--   **Formalization Note** The inner function has a subtype as its carrier. It is never required to extend submodularly to the outer carrier. The operation itself is total; positivity and the other hypotheses are stated by Lemma 2.1.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Lemma 2.1, printed p. 7 / PDF p. 8

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin

/-- The actual inner ground set, rather than a globally submodular extension. -/
abbrev InnerGround {n : ℕ} (P R : Finset (Fin n)) := {x : Fin n // x ∉ P ∪ R}

def innerQuery {n : ℕ} (P R S : Finset (Fin n)) : Finset (InnerGround P R) :=
  Finset.univ.filter fun x => x.val ∈ S

/-- Lemma 2.1's nesting operation. In its recursive branch `innerQuery` represents `S \ P`.
The first two branches are multiplied by `w`, never exponentiated. -/
noncomputable def nest {n : ℕ} (P R : Finset (Fin n)) (w : ℕ)
    (g : Finset (InnerGround P R) → ℝ) (S : Finset (Fin n)) : ℝ :=
  if ¬ Disjoint S R then
    (w : ℝ) * n * (Finset.univ \ S).card
  else if ¬ P ⊆ S then
    (w : ℝ) * S.card
  else g (innerQuery P R S)

end SFMQueryLower.EmptyMin


