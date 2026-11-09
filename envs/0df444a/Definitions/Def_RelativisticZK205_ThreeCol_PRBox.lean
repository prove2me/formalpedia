-- Prove2me | Definitions.Def_RelativisticZK205_ThreeCol_PRBox
-- name    : RelativisticZK205_ThreeCol_PRBox
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:08:09.03597+00:00
-- url     : https://prove2.me/theorems/144c04f4-862c-4600-9bdb-6c6bedcfb490
-- title:
--   The PR-box: output uniform among the solutions of $x\oplus y=a\wedge b$
-- statement:
--   The **PR-box** is the two-party channel with one-bit inputs $a,b\in\mathbb F_2$ and one-bit outputs $x,y\in\mathbb F_2$ that outputs $(x,y)$ uniformly among the solutions of the CHSH condition
--
--   $$
--   x\oplus y=a\wedge b.
--   $$
--
--   Each input pair has exactly two solutions, so each has probability $1/2$. The PR-box is the basic nonlocal resource used by the simulators' comparators in Steps 4–5 of §5.1.
--
--   **Formalization Note** Bits are `Bool`, $\oplus$ is `xor` and $\wedge$ is `&&`; the output is `PMF.uniformOfFinset` on the solution set, which is shown nonempty in the file.
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.6, Fig. 6

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Channel

/-!
# The PR-box

Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, *Relativistic Zero
Knowledge*, STOC 2027 submission #205 (October 2026), p.6, Fig. 6.
-/

namespace RelativisticZK205.ThreeCol

/-- The solutions `(x, y)` of the CHSH condition `a ∧ b = x ⊕ y` for inputs `a, b`. -/
def prSolutions (a b : Bool) : Finset (Bool × Bool) :=
  Finset.univ.filter fun p => xor p.1 p.2 = (a && b)

lemma prSolutions_nonempty (a b : Bool) : (prSolutions a b).Nonempty :=
  ⟨(a && b, false), by simp [prSolutions]⟩

/-- Fig. 6, p.6: the PR-box. On inputs `a` (Alice) and `b` (Bob) it outputs `(x, y)` uniformly among
the solutions of `a ∧ b = x ⊕ y`. Bits of `F₂` are `Bool`, `⊕` is `xor` and `∧` is `&&`. -/
noncomputable def prBox : Channel Bool Bool Bool Bool := fun a b =>
  PMF.uniformOfFinset (prSolutions a b) (prSolutions_nonempty a b)

end RelativisticZK205.ThreeCol


