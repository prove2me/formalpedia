-- Prove2me | Definitions.Def_BarelyTestable_LowerBound_Padding
-- name    : BarelyTestable_LowerBound_Padding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:22:28.237512+00:00
-- url     : https://prove2.me/theorems/df08c7c0-4732-4df0-bc7f-dd03bd6cde64
-- title:
--   Projection simulation and block size for arbitrary larger dimensions
-- statement:
--   For dimensions $d\le N$, projection sends an $N$-vertex to its first $d$ coordinates, and padding sets $\widetilde f(S)=f(\operatorname{project}(S))$. A simulator replays the large-domain procedure using the same exact answers already observed, retains its original query vertices internally, and projects the next query to the small domain. It therefore uses one source query per requested large-domain query and preserves stopping and output.
--
--   The selected block size is
--
--   $$m=\left\lfloor\sqrt{(N-2)/2}\right\rfloor,$$
--
--   computed by integer division and integer square root. These definitions supply the representation for the padding step acknowledged on p.11. Preservation of submodularity, exact farness, run output and query budget are proof obligations, documented in the local moderation notes; they are not structure fields or assumptions in the goal.
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), §3 all-large-dimension padding observation; proof of Theorem 3.1, p. 11, 26 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Protocol
import Definitions.Def_BarelyTestable_LowerBound_Construction

set_option autoImplicit false

namespace BarelyTestable.LowerBound

/-- Replay the large-domain procedure using exactly the answers recorded by the small-domain
simulator. Query vertices in the small transcript are redundant: they were computed by this replay. -/
def replay {d N : ℕ} (A : Procedure (Fin N)) (h : History (Fin d)) : History (Fin N) :=
  h.foldl (fun hN p => match A hN with
    | Sum.inl _ => hN
    | Sum.inr x => hN ++ [(x, p.2)]) []

/-- Simulation uses only projected queries; every source query costs one simulator query. -/
def simulate {d N : ℕ} (A : Procedure (Fin N)) : Procedure (Fin d) := fun h =>
  match A (replay A h) with
  | Sum.inl b => Sum.inl b
  | Sum.inr x => Sum.inr (projectVertex x)

/-- floor(sqrt((N-2)/2)), with integer division before integer square root. -/
def paddingBlockSize (N : ℕ) : ℕ := Nat.sqrt ((N - 2) / 2)

end BarelyTestable.LowerBound


