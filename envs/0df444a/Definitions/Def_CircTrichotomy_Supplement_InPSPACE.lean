-- Prove2me | Definitions.Def_CircTrichotomy_Supplement_InPSPACE
-- name    : CircTrichotomy_Supplement_InPSPACE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:12:45.83004+00:00
-- url     : https://prove2.me/theorems/36f9a2e2-ea39-4378-8c3d-c546fb366217
-- title:
--   PSPACE and PSPACE-completeness under logarithmic-space many-one reductions
-- statement:
--   A language $L\subseteq\{0,1\}^*$ is in **PSPACE** if some deterministic multitape machine with a read-only input tape halts on every input, accepts exactly the strings of $L$, and uses at most $p(|x|)$ work-tape cells on input $x$, for a polynomial $p$, at every step of the run.
--
--   $L$ is **PSPACE-hard under logarithmic-space reductions** if for every language $L'$ in PSPACE there is a map $f:\{0,1\}^*\to\{0,1\}^*$ computable by a deterministic transducer using $O(\log |x|)$ work space such that
--   $$x\in L' \iff f(x)\in L \qquad\text{for all } x.$$
--   $L$ is **PSPACE-complete under logarithmic-space reductions** if it is in PSPACE and PSPACE-hard under logarithmic-space reductions.
--
--   These are the notions of Theorem 4.1, whose lower bound (Proposition F.6) is stated under logarithmic-space reductions.
--
--   **Formalization Note** The machines are the published model `ArrighiStarFree.HalfLevel.SpaceMachine` (space = visited work cells, blank or written, summed over all work tapes), and the reductions are its published `LogspaceComputable`. The polynomial has natural-number coefficients, which dominates every polynomial bound. PSPACE is defined with deterministic machines; nondeterministic polynomial space gives the same class by Savitch's theorem.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 4.1, p.10; Proposition F.5, p.69; Proposition F.6, p.70; §7, p.13

import Mathlib
import Definitions.Def_ArrighiStarFree_HalfLevel_SpaceMachine

set_option autoImplicit false

namespace CircTrichotomy

namespace Supplement

open ArrighiStarFree.HalfLevel

/-- **PSPACE** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*,
arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 4.1, p.10; Proposition
F.5, p.69), in the published machine model `ArrighiStarFree.HalfLevel.SpaceMachine` (read-only
input tape with end-markers, finitely many work tapes, write-only output). A language
`L ⊆ {0,1}*` is in PSPACE if some *deterministic* machine halts on every input, accepts exactly
the strings of `L`, and a polynomial `p` bounds the total number of work-tape cells visited, at
every step of every run, by `p(|x|)`.

**Formalization Note** The space measure is the published one (visited cells, blank or written,
summed over all work tapes). The polynomial has natural-number coefficients; every polynomial
bound is dominated by one of these. PSPACE is defined with deterministic machines; the paper's
nondeterministic polynomial-space procedure (p.70) gives the same class by Savitch's theorem. -/
def InPSPACE (L : Set (List Bool)) : Prop :=
  ∃ (M : SpaceMachine) (p : Polynomial ℕ), M.Deterministic ∧
    (∀ x choices t, (∑ i : Fin (M.tapes + 1), (M.run x choices t).visited i) ≤ p.eval x.length) ∧
    (∀ x, M.Halts x) ∧ ∀ x, (M.Accepts x ↔ x ∈ L)

/-- **PSPACE-hardness under logarithmic-space reductions** (Proposition F.6, p.70: "is
PSPACE-hard under logarithmic space reductions"; §7, p.13): every language `L'` in PSPACE
many-one reduces to `L` by a deterministic log-space computable map `f` (the published
`LogspaceComputable`): `x ∈ L' ↔ f x ∈ L` for every `x`. -/
def PSPACEHardLog (L : Set (List Bool)) : Prop :=
  ∀ L' : Set (List Bool), InPSPACE L' →
    ∃ f : List Bool → List Bool, LogspaceComputable f ∧ ∀ x, x ∈ L' ↔ f x ∈ L

/-- **PSPACE-complete under logarithmic-space reductions** (Theorem 4.1, p.10; Proposition F.5,
p.69; Proposition F.6, p.70): in PSPACE and PSPACE-hard under log-space many-one reductions. -/
def PSPACECompleteLog (L : Set (List Bool)) : Prop :=
  InPSPACE L ∧ PSPACEHardLog L

end Supplement

end CircTrichotomy


