-- Prove2me | Definitions.Def_KTUnitary_Synth_queries
-- name    : KTUnitary_Synth_queries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:05.417266+00:00
-- url     : https://prove2.me/theorems/7586b0e3-ad87-4ef3-8bad-781eb783a5c4
-- title:
--   Oracle queries made by a run of a machine
-- statement:
--   For a deterministic oracle Turing machine $M$, an oracle $O$, an input $s$ and a step count $T$, the list of strings written on the query tape at the steps $t<T$ at which the run of $M^O$ on $s$ is in its query state.
--
--   It expresses the restriction in $\mathsf{FNEXP}^L[\mathrm{poly}]$ that the machine only queries $L$ on strings of length at most $\mathrm{poly}(|x|)$.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.2, p. 34

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **The oracle queries of a run** (needed for Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.2, p. 34: `FNEXP^L[poly]`
machines are "restricted to only query `L` on strings of length at most `poly(|x|)`"): the list
of strings on the query tape at the steps `t < T` at which the run of `M^O` on `s` is in the
query state (state `3`). -/
def queries (M : OTM) (O : Oracle) (s : Str) (T : ℕ) : List Str :=
  (List.range T).filterMap fun t =>
    let c := M.runCfg O s t
    if c.state = 3 then some (OTM.readBits c.query c.qhi) else none

end KTUnitary.Synth


