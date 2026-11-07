-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_psAccepts
-- name    : QAdvFew_PoQOracle_psAccepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:31.575871+00:00
-- url     : https://prove2.me/theorems/b4089475-5c62-4bd2-8c79-c770bfe6e7b1
-- title:
--   Acceptance as a member of $S_t^{\mathsf{PSPACE}}$
-- statement:
--   $S_t^{\mathsf{PSPACE}}$ is the set of pairs $(M,x)$ taking fewer than $t$ bits to specify, with $M$ syntactically restricted to run in at most $2^t$ steps, use space at most $t$, and query only the oracles $\mathcal O_1,\dots,\mathcal O_{\lfloor\sqrt t\rfloor}$. This predicate says that $M^O(x)$ has accepted within $2^t$ steps using at most $t$ cells.
--
--   **Formalization Note** The restrictions are read as clocks: a machine that has not accepted within $2^t$ steps, or has used more than $t$ cells, counts as rejecting. For a machine meeting them this is its acceptance.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §4.1, pp. 21–22 (PDF pp. 23–24)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- `M^O(x)` accepts as a member of `S^PSPACE_t` (Goldin, Lombardi, Morimae, *Quantum Advantage has
Few Complexity Implications*, arXiv:2611.05303v1, §4.1, pp. 21–22 (PDF pp. 23–24): "(a) `M` runs in
at most `2^t` steps (b) `M` uses space at most `t`"): `M^O(x)` has accepted within `2^t` steps, using
at most `t` cells.

**Formalization Note** The syntactic restrictions are read as clocks: a machine that has not
accepted within `2^t` steps, or has used more than `t` cells, counts as rejecting. For a machine
meeting the restrictions this is its acceptance. -/
def psAccepts (M : OTM) (O : Oracle) (x : Str) (t : ℕ) : Prop :=
  M.result O x (2 ^ t) = some true ∧ M.space O x (2 ^ t) ≤ t

end QAdvFew.PoQOracle


