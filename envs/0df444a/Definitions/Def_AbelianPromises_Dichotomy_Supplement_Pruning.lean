-- Prove2me | Definitions.Def_AbelianPromises_Dichotomy_Supplement_Pruning
-- name    : AbelianPromises_Dichotomy_Supplement_Pruning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:53:35.760198+00:00
-- url     : https://prove2.me/theorems/ea15ea98-6da0-4ac9-a0ba-1cf026d081c2
-- title:
--   Constraint singleton AIP pruning and kappa
-- statement:
--   One CSinglAIP round tests the pinned AIP system for each currently surviving constraint tuple and deletes that tuple from its own constraint exactly when the test is infeasible. Repeating these rounds gives the fixed point. If $N_0$ is the initial total number of stored tuples, $N_0+1$ rounds suffice, since a nonstationary round deletes a tuple and tuples never return.
--
--   The construction $\kappa$ then restricts each nonisolated variable domain to values compatible with every surviving incident constraint; isolated domains remain unchanged:
--
--   $$
--   D'_x=\{a\in D_x:\ \forall(C,i)\text{ with }x_i=x,\ \exists t\in R_C\text{ with }t_i=a\}.
--   $$
--
--   Rejection, including empty initial domains or relations, is represented separately and has no minion solution. Feasibility is specified by the actual signed integer equations, and no satisfying assignment, affine certificate, minion map, or oracle is an input. This construction supplies the concrete pruning operation used in the supplement.
--
--   **Formalization Note** Simultaneous deletion rounds implement the same greatest fixed point as exhaustive sequential deletions. The bound $N_0+1$ is a termination bound for this denotation, not an assumed polynomial-time integer-solving oracle.
-- source:
--   Tamio-Vesa Nakajima, Zephyr Verwimp, Stanislav Živný, STOC 2027 submission #967 (October 2026). Canonical submission artifact; no arXiv pin or acceptance claim. printed p. 16 (PDF p. 17), Definition C.6; printed p. 20 (PDF p. 21), definition of kappa preceding Lemma C.12.

import Mathlib
import Definitions.Def_AbelianPromises_Dichotomy_Supplement_CurrentCSP

set_option autoImplicit false

namespace AbelianPromises.Dichotomy.Supplement

/-- One simultaneous deletion round of Definition C.6. Feasibility is a mathematical
specification of integer-system solving, not a supplied oracle or certificate. -/
noncomputable def pruneRound (I : CurrentCSP) : CurrentCSP := by
  classical
  exact { I with tuples := fun c => (I.rel c).filter fun t => AIPFeasible (pinConstraint I c t) }

/-- There are at most this many strict tuple-deletion rounds. An extra round also covers
initial incompatible tuples. Empty constraints stay empty. -/
noncomputable def pruningFixedPoint (I : CurrentCSP) : CurrentCSP :=
  (pruneRound^[1 + ∑ c, (I.tuples c).card]) I

/-- Retain all incident compatibility conditions; an isolated domain is unchanged. -/
def restrictDomains (I : CurrentCSP) : CurrentCSP :=
  { I with domain := fun x => (I.domain x).filter fun a =>
      ∀ (c : Fin I.m) (i : Fin (I.arity c)), I.scope c i = x →
        ∃ t ∈ I.rel c, t i = a }

/-- Kappa of Appendix C.3: run actual tuple pruning, then restrict domains. None denotes
rejection; in particular empty initial domains/relations are explicitly unsatisfiable. -/
noncomputable def kappa (I : CurrentCSP) : Option CurrentCSP := by
  classical
  let J := restrictDomains (pruningFixedPoint I)
  exact if (∀ x, (J.domain x).Nonempty) ∧ (∀ c, (J.rel c).Nonempty) then some J else none

end AbelianPromises.Dichotomy.Supplement


