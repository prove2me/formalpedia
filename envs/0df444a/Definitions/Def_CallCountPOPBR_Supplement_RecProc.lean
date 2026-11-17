-- Prove2me | Definitions.Def_CallCountPOPBR_Supplement_RecProc
-- name    : CallCountPOPBR_Supplement_RecProc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:01:35.775701+00:00
-- url     : https://prove2.me/theorems/95d153fa-12ac-4322-a1f2-c52f4fe1cd72
-- title:
--   Terminating recursive procedures and their invocation counts
-- statement:
--   A **terminating recursive procedure** on an input type $X$ assigns to each input $x$ an ordered list of child inputs. Repetitions are allowed, and the relation “$y$ is a child of $x$” is well founded. An input is a base case exactly when its child list is empty.
--
--   Its total invocation count is the well-founded recursive function
--
--   $$
--   C(x)=1+\sum_{y\text{ in the child list of }x} C(y),
--   $$
--
--   with repeated children counted repeatedly and the empty sum equal to zero.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884…), Scope, p.3, and Eq. (5), p.8

import Mathlib

set_option autoImplicit false

namespace CallCountPOPBR.Supplement

universe u

/-- **A terminating recursive procedure** (§4). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), §4, p.8: "Let x denote an input, and suppose
an invocation on x generates child inputs x_1, …, x_{r(x)}"; Scope, p.3: "All calls terminate;
memoisation and caching are excluded."

`ch x` is the ordered list of child inputs `x_1, …, x_{r(x)}` of an invocation on `x` (repetitions
allowed); `x` is a base case iff `ch x = []`. The call relation "`y` is a child of `x`" is well
founded (all calls terminate). -/
structure RecProc (X : Type u) where
  /-- The child inputs of an invocation on `x`, in order. -/
  ch : X → List X
  /-- All calls terminate: the call relation is well founded. -/
  wf : WellFounded (fun y x : X => y ∈ ch x)

/-- **The total invocation count `C(x)`** (§4, Eq. (5), p.8): "C(x) = 1 + ∑_{i=1}^{r(x)} C(x_i),
where the empty sum is zero", defined by well-founded recursion on the call relation. -/
noncomputable def RecProc.count {X : Type u} (P : RecProc X) : X → ℕ :=
  P.wf.fix (fun x IH => 1 + ((P.ch x).attach.map (fun y => IH y.1 y.2)).sum)

end CallCountPOPBR.Supplement


