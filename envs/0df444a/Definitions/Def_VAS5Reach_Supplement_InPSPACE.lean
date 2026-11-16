-- Prove2me | Definitions.Def_VAS5Reach_Supplement_InPSPACE
-- name    : VAS5Reach_Supplement_InPSPACE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:47:31.818576+00:00
-- url     : https://prove2.me/theorems/572331b9-9ecb-4f20-816d-86d9abc12f3a
-- title:
--   PSPACE, and PSPACE- and NL-completeness under log-space reductions
-- statement:
--   In the multitape machine model of the published `ArrighiStarFree.HalfLevel.SpaceMachine` (finite control, read-only input tape, work tapes, write-only output, space measured by the number of work-tape cells visited), a problem is in **PSPACE** if a deterministic machine halts on every input, decides the problem, and visits at most $p(n)$ work cells on inputs of length $n$, for a polynomial $p$.
--
--   A language $L\subseteq\{0,1\}^*$ is
--
--   1. **PSPACE-complete** if it is in PSPACE and every language $A$ in PSPACE reduces to it by a map $f$ computed by a deterministic log-space transducer with $x\in A\iff f(x)\in L$;
--   2. **NL-complete** if it is in NL (the published `InNL`) and every language in NL reduces to it in the same way.
--
--   These are the classes and the completeness notions of Theorem 1.1.
--
--   **Formalization Note** NL, PSPACE and log-space reductions are all taken in one machine model; the reductions are log-space many-one reductions (the published `HardFor … LogspaceComputable`).
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 1.1, p.2 (PDF p.4); App. A.1, p.44 (PDF p.46)

import Mathlib
import Definitions.Def_ArrighiStarFree_HalfLevel_SpaceMachine
import Definitions.Def_ArrighiStarFree_HalfLevel_Reductions

namespace VAS5Reach.Supplement

open ArrighiStarFree.HalfLevel

/-- **PSPACE** in the published multitape machine model `ArrighiStarFree.HalfLevel.SpaceMachine`
(read-only input tape, finitely many work tapes, write-only output): a problem is in PSPACE if a
*deterministic* machine halts on every input, decides the problem on its domain, and a polynomial
`p` bounds the total number of work-tape cells visited, at every step of every run, by
`p(|x|)`.

Source: used in W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems
Is PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 1.1, printed p. 2
(PDF p. 4); App. A.1, printed p. 44 (PDF p. 46): "in NPSPACE = PSPACE".

**Formalization Note** The model is the one of the published `InNL` (same machines, same space
measure), so NL, PSPACE and log-space reductions live in one machine model. -/
def InPSPACE (P : PromiseProblem) : Prop :=
  ∃ (M : SpaceMachine) (p : Polynomial ℕ), M.Deterministic ∧
    (∀ x choices t, (∑ i : Fin (M.tapes + 1), (M.run x choices t).visited i) ≤ p.eval x.length) ∧
    (∀ x, M.Halts x) ∧ ∀ x ∈ P.domain, (M.Accepts x ↔ P.answer x)

/-- A language is **PSPACE-complete** (under log-space many-one reductions): it is in PSPACE and
every language in PSPACE reduces to it by a deterministic log-space computable map `f` with
`x ∈ A ↔ f x ∈ L` (the published `HardFor … LogspaceComputable`). -/
def PSPACECompleteLog (L : Set (List Bool)) : Prop :=
  InPSPACE (totalProblem L) ∧ HardFor InPSPACE LogspaceComputable (totalProblem L)

/-- A language is **NL-complete** (under log-space many-one reductions): it is in NL (the published
`InNL`) and every language in NL reduces to it by a deterministic log-space computable map. -/
def NLCompleteLog (L : Set (List Bool)) : Prop :=
  InNL (totalProblem L) ∧ HardFor InNL LogspaceComputable (totalProblem L)

end VAS5Reach.Supplement


