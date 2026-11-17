-- Prove2me | Definitions.Def_AvoidPlast_Supplement_SolvesAvoidNDB
-- name    : AvoidPlast_Supplement_SolvesAvoidNDB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:57:57.251885+00:00
-- url     : https://prove2.me/theorems/7f1e2a60-1f33-43ae-83cf-37a496c4631d
-- title:
--   Solving Avoid with $g(n)$ non-deterministic bits
-- statement:
--   A non-deterministic machine $A$ *solves* $\mathrm{Avoid}_C$ on $x$ with $g(n)$ non-deterministic bits if some witness of length at most $g(|x|)$ is accepted, and on every accepted witness of that length the output is an $\ell_{out}(|x|)$-bit string outside $\mathrm{Range}(C_x)$.
--
--   This is the success notion of $\mathrm{SearchNTimeGuess}$ (Definition 3.5) and of Theorems 6.9 and 6.11 ("on some witness $A(x)$ outputs an Avoid solution, and for every witness it outputs either an Avoid solution or $\bot$").
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 3.5, p.14; Theorem 6.9, p.37

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_SolvesAvoid
import Definitions.Def_AvoidPlast_output

namespace AvoidPlast.Supplement

open AvoidPlast

/-- A non-deterministic algorithm using at most `g(n)` non-deterministic bits solves `Avoid_C`
on `x` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 3.5, p.14; Theorem 6.9, p.37): on some witness of length at most
`g(|x|)` it accepts, and on every accepting witness of that length its output is an `Avoid_C`
solution. A rejecting witness is the output `⊥`. -/
def SolvesAvoidNDB (A : Machine 2) (C : List Bool → List Bool → List Bool) (ℓin ℓout g : ℕ → ℕ)
    (x : List Bool) : Prop :=
  (∃ w : List Bool, w.length ≤ g x.length ∧ Accepts A ![x, w]) ∧
    ∀ w : List Bool, w.length ≤ g x.length → Accepts A ![x, w] →
      SolvesAvoid C ℓin ℓout x (output A ![x, w])

end AvoidPlast.Supplement


