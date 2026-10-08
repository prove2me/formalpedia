-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_recurrentClasses
-- name    : YoungConventions_RiskDominance_recurrentClasses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:15.703089+00:00
-- url     : https://prove2.me/theorems/62901df0-7e82-46c9-a1e0-289ffc8eacf6
-- title:
--   Recurrent communication classes of a finite Markov chain
-- statement:
--   Let $P$ be a transition matrix on a finite set $X$. A state $x$ is **recurrent** if every state accessible from $x$ can access $x$ back. The **recurrent communication class** of a recurrent state $x$ is the set of states accessible from $x$. The set of recurrent communication classes of $P$ is
--   $$\{\,\{y : y\text{ accessible from }x\} : x\text{ recurrent}\,\}.$$
--   In the paper these are the classes $H_1,\dots,H_J$ of the unperturbed process $P^0$.
--
--   **Formalization Note** On a finite state space, recurrence coincides with this "essential state" property. The page (p. 68) writes "the recurrent communication classes of $P^\varepsilon$", a slip: $P^\varepsilon$ is irreducible, and the properties (i)–(iii) listed after it are about paths of zero resistance, i.e. about $P^0$ (as in the Appendix, p. 77). The mission applies this definition to $P^0$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 68 (slip P^ε for P⁰ corrected); Appendix, p. 77

import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain

namespace YoungConventions.RiskDominance

/-- **Recurrent communication classes of a finite Markov chain.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 68 (PDF p. 13):
"Let `H₁, H₂, …, H_J` be the recurrent communication classes of `P⁰`" (the page prints `P^ε`; see
the note), and Appendix, p. 77 (PDF p. 22): "Let the recurrent communication classes of `P⁰` be
denoted by `X₁, …, X_J`."

A state `x` is recurrent if every state reachable from `x` can reach `x` back; the recurrent
communication class of a recurrent `x` is the set of states reachable from `x`.
`recurrentClasses P` is the set of these classes.

**Formalization Note.** On a finite state space, a state is recurrent iff it is essential in this
sense, and its class is then closed and communicating. **Corrected slip:** p. 68 says "the recurrent
communication classes of `P^ε`"; `P^ε` is irreducible (its only class is the whole space) and the
properties (i)–(iii) listed next are about zero-resistance paths, i.e. `P⁰`. The mission applies this
definition to `P⁰ = unperturbed p`. -/
def recurrentClasses {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ) : Set (Set X) :=
  {C | ∃ x, (∀ y, YoungConventions.Perturbed.Reaches P x y → YoungConventions.Perturbed.Reaches P y x) ∧ C = {y | YoungConventions.Perturbed.Reaches P x y}}

end YoungConventions.RiskDominance


