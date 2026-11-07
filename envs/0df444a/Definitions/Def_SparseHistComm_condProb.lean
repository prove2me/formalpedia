-- Prove2me | Definitions.Def_SparseHistComm_condProb
-- name    : SparseHistComm_condProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:38:09.769003+00:00
-- url     : https://prove2.me/theorems/13681d18-b564-4ed5-acb1-2ec00ac2467d
-- title:
--   Analysis probability given $R = r$
-- statement:
--   The **conditional probability given $R = r$** of an event $E(X, M)$ under the analysis prior of Section IV is the conditional expectation of its indicator, $P(E \mid R = r) = E[\mathbf 1_E \mid R = r]$. For example $P(J_i \ge j, |M_i| < jL \mid R = r)$ in the proof of Lemma 2.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section IV, p.8; proof of Lemma 2, p.15

import Mathlib
import Definitions.Def_SparseHistComm_condExp
open scoped ENNReal

namespace SparseHistComm

open Classical in
/-- The **analysis probability given `R = r`** of an event `E(X, M)` (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section IV, p.8, and
proof of Lemma 2, p.15, e.g. `P(Jᵢ ≥ j, |Mᵢ| < jL | R = r)`): the conditional analysis
expectation of its indicator. -/
noncomputable def condProb {n d : ℕ} (P : Protocol n d) (k : ℕ) (r : P.Ω)
    (E : (Fin n → Finset (Fin d)) → (Fin n → List Bool) → Prop) : ℝ≥0∞ :=
  condExp P k r (fun X m => if E X m then 1 else 0)

end SparseHistComm


