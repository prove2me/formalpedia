-- Prove2me | Definitions.Def_PhyloCSP_ConstraintLanguage
-- name    : PhyloCSP_ConstraintLanguage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:24:57.750347+00:00
-- url     : https://prove2.me/theorems/bf392cf2-78e1-44b3-8ced-0779a806e3e9
-- title:
--   Constraint languages $\Pi$
-- statement:
--   A **constraint language** $\Pi$ is a finite nonempty set of phylogenetic predicates, possibly of different arities (Definition 1.2). It is represented as a finite nonempty family $(\varphi_i)_{i\in\iota}$, where $\varphi_i$ has arity $k_i$ and is given by its satisfying set.
--
--   **Formalization Note** A set is encoded as an indexed family; repetitions do not change any minimum over the language. Section 2 remarks that one may assume, without loss of generality, that $\Pi$ contains no always-true or always-false predicates; that convention is not imposed here.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 1.2, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_PhyloCSP_Predicate

set_option autoImplicit false

namespace PhyloCSP

/-- **Constraint languages.**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 1.2, p.1 (PDF p.3): "A phylogenetic constraint
satisfaction problem CSP(Π) is specified by a finite nonempty set of phylogenetic predicates Π,
called the constraint language."

A constraint language is a finite nonempty family `(φᵢ)_{i ∈ ι}` of predicates; `φᵢ` has arity
`arity i` and satisfying set `sat i`.

**Formalization Note.** A finite nonempty *set* is encoded as a finite nonempty indexed family
(repetitions change no minimum over the language). Section 2's convention "Π contains neither
always-true nor always-false predicates" (p.6) is a without-loss-of-generality remark, not part of
Definition 1.2, and is not imposed. -/
structure ConstraintLanguage where
  /-- The index set of the predicates. -/
  ι : Type
  [fintype : Fintype ι]
  [nonempty : Nonempty ι]
  /-- The arity of each predicate. -/
  arity : ι → ℕ
  /-- The satisfying set of each predicate. -/
  sat : ∀ i, Predicate (arity i)

attribute [instance] ConstraintLanguage.fintype ConstraintLanguage.nonempty

end PhyloCSP


