-- Prove2me | Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_BinLoad
-- name    : LinearHashingPoissonesque_ExpectedLoads_BinLoad
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T19:01:15.574862+00:00
-- url     : https://prove2.me/theorems/dea479ae-9a62-4024-a526-813ce7004c15
-- title:
--   Load of a labelled bin
-- statement:
--   Let $S$ be a finite subset of a set $A$, let $B$ be a set of bins, and let $f:A\to B$ be any function. The load of a bin $y\in B$ is
--
--   $$L_y(S,f)=|\{s\in S:f(s)=y\}|.$$
--
--   The value is defined for every bin, including bins with no preimage in $S$, whose load is zero. This basic count is shared by the labelled load vector, the ordered statistics and the potentials. It imposes no linearity on $f$.
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.8, Section 2, Load Statistics; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf

import Mathlib

namespace LinearHashingPoissonesque.ExpectedLoads

/-- Section 2, p.8: the load of a labelled bin, including empty bins. -/
noncomputable def binLoad {A B : Type*} (S : Finset A) (f : A → B) (y : B) : ℕ :=
  haveI := Classical.decEq B
  (S.filter (fun s => f s = y)).card

end LinearHashingPoissonesque.ExpectedLoads


