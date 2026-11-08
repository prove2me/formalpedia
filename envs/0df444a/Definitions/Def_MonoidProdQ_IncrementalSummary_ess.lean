-- Prove2me | Definitions.Def_MonoidProdQ_IncrementalSummary_ess
-- name    : MonoidProdQ_IncrementalSummary_ess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:49:37.437234+00:00
-- url     : https://prove2.me/theorems/dcdd9155-d395-456d-9bc8-f3bc3a825d09
-- title:
--   Essential positions $\mathrm{Ess}_x(T)$ of a summary
-- statement:
--   For an incremental summary with states $s_x(T)$, the **essential positions** of a revealed index set $T\subseteq I$ on input $x$ are
--
--   $$\mathrm{Ess}_x(T)=\{\,i\in T : s_x(T)\ne s_x(T\setminus\{i\})\,\}:$$
--
--   the revealed positions whose removal would change the summary state.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Definition 2, p.27

import Definitions.Def_MonoidProdQ_IncrementalSummary

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Definition 2, p.27: "For input x, the essential positions of a revealed index set
T ⊆ I are Essₓ(T) = {i ∈ T : sₓ(T) ≠ sₓ(T \ {i})}". -/
def IncrementalSummary.ess {I Sig Out Q : Type*} [DecidableEq I] [Fintype I] [DecidableEq Q]
    {f : (I → Sig) → Out} {D : Finset (I → Sig)} (S : IncrementalSummary f D Q)
    (x : I → Sig) (T : Finset I) : Finset I :=
  T.filter fun i => S.s x T ≠ S.s x (T.erase i)

end MonoidProdQ


