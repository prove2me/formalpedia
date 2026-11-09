-- Prove2me | Definitions.Def_QStateSearch_numQueries
-- name    : QStateSearch_numQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:18.674574+00:00
-- url     : https://prove2.me/theorems/65557c45-2e38-4f98-a1e4-6cb92c014349
-- title:
--   Number of query slots $q$
-- statement:
--   The number of query slots of a verifier $V$ is the number of oracle-query steps in its step list. Every execution of a fixed step list has the same chronologically ordered query slots, which the paper arranges by padding. The theorems assume $\mathrm{numQueries}(V)\le q$.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.2, p.10

import Mathlib
import Definitions.Def_QStateSearch_Verifier

namespace QStateSearch

/-- The number of oracle-query slots of a verifier, `q` in the paper.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.2, p.10 ("Every execution then has the same chronologically ordered list of
query slots").

**Formalization Note.** In a fixed step list every execution has the same query slots, as the
paper arranges by padding. The theorems take a bound `numQueries V ≤ q`. -/
def numQueries {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (V : Verifier D W) : ℕ :=
  V.steps.countP fun s => match s with
    | .query => true
    | _ => false

end QStateSearch


