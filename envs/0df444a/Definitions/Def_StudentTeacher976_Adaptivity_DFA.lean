-- Prove2me | Definitions.Def_StudentTeacher976_Adaptivity_DFA
-- name    : StudentTeacher976_Adaptivity_DFA
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T00:48:25.306736+00:00
-- url     : https://prove2.me/theorems/24d8291b-befa-4aea-ab58-03c6cb72a7d3
-- title:
--   Finite automata for tuple syntax checks
-- statement:
--   A finite deterministic automaton consists of a finite state set, one initial state, a binary transition function, and an accepting-state predicate. Its run on a word is
--
--   $$
--   \delta^*(q_0,b_1\cdots b_m)=\delta(\cdots\delta(\delta(q_0,b_1),b_2)\cdots,b_m).
--   $$
--
--   This interface supplies the finite syntax checks used before an oracle-machine computation. It includes no language-class membership or runtime assertion.
-- source:
--   Implementation bridges for Ježil–Tsintsilidas, STOC 2027 submission #976 (October 2026), §1.2.1 pp.6–7, §3.1 p.19; finite oracle machines and tuple parsing in the pinned formalization; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf Standard automaton interface: Mathlib, Mathlib/Computability/DFA.lean, structure DFA, pinned revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_StudentTeacher976_Adaptivity_Complexity

namespace QAdvFew.PoQOracle.OTM.Precheck

/-- A finite deterministic automaton on words, used for the tuple syntax checks. -/
structure DFA where
  size : ℕ
  start : Fin size
  next : Fin size → Bool → Fin size
  accept : Fin size → Bool

/-- Process the complete input word. -/
def DFA.run (D : DFA) (x : List Bool) : Fin D.size := x.foldl D.next D.start

end QAdvFew.PoQOracle.OTM.Precheck


