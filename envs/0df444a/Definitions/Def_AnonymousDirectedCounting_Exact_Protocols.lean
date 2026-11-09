-- Prove2me | Definitions.Def_AnonymousDirectedCounting_Exact_Protocols
-- name    : AnonymousDirectedCounting_Exact_Protocols
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:11.865914+00:00
-- url     : https://prove2.me/theorems/a7c452ce-72ae-4b8a-8f1f-20cad0e98a06
-- title:
--   The core and combined Counting algorithms
-- statement:
--   An agent's state is its current round $t$ and its vista at round $t$. In each round it adds a new bottom node with its old node as parent, the current outdegree as label, and the received states as red-edge tails.
--
--   The core algorithm outputs at round $t=2m-1$, for $m\ge\ell$, the candidate $m$ if the test with final level $\mathcal L_m$ accepts it, and otherwise produces no output. The combined algorithm first outputs $\ell$ at round $\ell$ if $\mathcal L_0$ has no nonleader node. Otherwise it tests $m=\ell+1,\ell+2,\dots$: at round $2m-1$ with final level $\mathcal L_m$ if $\ell=1$, and at round $2m-2$ with final level $\mathcal L_{m-1}$ if $\ell\ge2$.
--
--   Both are instances of the protocol interface: they see only $\ell$, leader status, received states and outdegree, and they read no population size, no fiber and no anonymity.
--
--   **Formalization Note** The output rule uses classical decidability of the test as a mathematical function; computing it is what the separate cost clause asserts. Received states at another level are discarded by the update, which never occurs on an execution because active agents share a round.
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Section 3.1, printed p. 6 (PDF p. 8); Section 3.2, printed p. 9 (PDF p. 11); Appendix C, printed pp. 19–20 (PDF pp. 21–22)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_CandidateTest

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact

open scoped Classical

noncomputable section

/-- An agent's state: its current level and its vista, written as a node of `History`. -/
abbrev VistaState : Type := Σ t : ℕ, History t

/-- The received states at the agent's own level, as red-edge tails of its new bottom node. Active
agents are all at one level, so on an execution nothing is dropped. -/
def inboxAt (t : ℕ) (msgs : Multiset VistaState) : Multiset (History t) :=
  msgs.filterMap (fun m => if hm : m.1 = t then some (hm ▸ m.2) else none)

/-- Vista construction: add the new bottom node with its parent, outdegree and red edges. -/
def vistaUpdate (s : VistaState) (msgs : Multiset VistaState) (d : ℕ) : VistaState :=
  ⟨s.1 + 1, ((s.2, d, inboxAt s.1 msgs) : History s.1 × ℕ × Multiset (History s.1))⟩

/-- Core algorithm (printed p. 6, PDF p. 8): at round `t = 2m - 1`, for `m ≥ ell`, run the test
on candidate `m` with final level `L_m`. Other rounds produce no output. -/
def coreOutput (s : VistaState) (ell : ℕ) : Option ℕ :=
  if s.1 % 2 = 1 ∧ ell ≤ (s.1 + 1) / 2 ∧ Accepts ell ((s.1 + 1) / 2) ((s.1 + 1) / 2) s.2
  then some ((s.1 + 1) / 2) else none

def coreProtocol : Protocol VistaState where
  initial := fun b => ⟨0, b⟩
  update := fun _ s msgs d => vistaUpdate s msgs d
  output := coreOutput

/-- Combined algorithm (printed pp. 9, 19-20, PDF pp. 11, 21-22). First, at round `ell`, output
`ell` if `L_0` has no nonleader node. Then test `m = ell + 1, ell + 2, ...`: at round `2m - 1` with
final level `L_m` if `ell = 1`, at round `2m - 2` with final level `L_{m-1}` if `ell ≥ 2`. -/
def sharpOutput (s : VistaState) (ell : ℕ) : Option ℕ :=
  if s.1 = ell ∧ nonleaderRoot ∉ vistaLevel s.1 s.2 0 then some ell
  else if ell = 1 then
    if s.1 % 2 = 1 ∧ ell + 1 ≤ (s.1 + 1) / 2 ∧ Accepts ell ((s.1 + 1) / 2) ((s.1 + 1) / 2) s.2
    then some ((s.1 + 1) / 2) else none
  else
    if s.1 % 2 = 0 ∧ ell + 1 ≤ (s.1 + 2) / 2 ∧ Accepts ell (s.1 / 2) ((s.1 + 2) / 2) s.2
    then some ((s.1 + 2) / 2) else none

def sharpProtocol : Protocol VistaState where
  initial := fun b => ⟨0, b⟩
  update := fun _ s msgs d => vistaUpdate s msgs d
  output := sharpOutput

end

end AnonymousDirectedCounting.Exact


