-- Prove2me | Definitions.Def_LaconicBarrier_Lang
-- name    : LaconicBarrier_Lang
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:39.172618+00:00
-- url     : https://prove2.me/theorems/58e81da2-3b00-4321-9597-ddb7fcefe5b5
-- title:
--   NP relations and their languages
-- statement:
--   For a relation $\mathcal R$ on bit strings, $L_{\mathcal R} = \{x : \exists w,\ (x, w) \in \mathcal R\}$. An **NP relation with witness bound $q$** is a polynomial-time decidable relation $\mathcal R$ (a polynomial-time predicate on $x\#w$) together with a polynomial $q$ such that every $(x, w) \in \mathcal R$ has $|w| \le q(|x|)$.
--
--   **Formalization Note** Polynomial-time predicates are the published `PolyPred2` (one-tape Turing machines on $x\#w$); the class of languages is NP.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.1, p.14; §4.1.2, p.16

import Mathlib
import Definitions.Def_KarpLiptonOM_PolyPred2

namespace LaconicBarrier

/-- The language `L_R = {x : ∃ w, (x, w) ∈ R}` of a relation (Jain, Mathialagan, Roy, STOC 2027
submission (manuscript sha256 1af78662…), §4.1.2, p.16). -/
def Lang (Rel : List Bool → List Bool → Prop) : Set (List Bool) := {x | ∃ w, Rel x w}

/-- An **NP relation** with witness bound `q` (Jain, Mathialagan, Roy, STOC 2027 submission
(manuscript sha256 1af78662…), §4.1, p.14: "an NP relation `R` is polynomial-time decidable. For each
such relation, fix a polynomial `q` such that every `(x, w) ∈ R` satisfies `m = |w| ≤ q(n)`"):
`R` is a polynomial-time predicate (the published `PolyPred2`) and `q` bounds its witnesses. -/
def IsNPRel (Rel : List Bool → List Bool → Prop) (q : Polynomial ℕ) : Prop :=
  KarpLiptonOM.PolyPred2 Rel ∧ ∀ x w, Rel x w → w.length ≤ q.eval x.length

end LaconicBarrier


