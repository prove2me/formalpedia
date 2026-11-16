-- Prove2me | Definitions.Def_MinorFreeOracle_LinearSpace_Supplement_ExactOracleParam
-- name    : MinorFreeOracle_LinearSpace_Supplement_ExactOracleParam
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:14:13.805359+00:00
-- url     : https://prove2.me/theorems/1d86056a-6329-46dd-8cb0-11c7f9da878b
-- title:
--   Deterministic exact distance oracles with a trade-off parameter given as input
-- statement:
--   Let $\mathrm{Pre}$ and $\mathrm{Qry}$ be finite programs of the comparison–addition word RAM, let $G$ be a finite weighted graph with $n$ vertices and $m$ edges, and let $k\ge 0$ be an integer parameter. The predicate $\mathrm{IsExactOracleParam}(\mathrm{Pre},\mathrm{Qry},G,k,T_{\mathrm{pre}},S,T_q)$ says that the pair of programs is a deterministic exact distance oracle for $G$ with parameter $k$:
--
--   1. the preprocessing program, started on the input $n, m, k$, the edge endpoints and the edge weights, halts within $T_{\mathrm{pre}}$ steps;
--   2. the memory it leaves behind costs at most $S$ cells, counting every distinct cell it writes plus all $3+3m$ input cells;
--   3. from that same stored memory, for every pair of vertices $s,t$, the query program started with $s,t$ halts within $T_q$ steps and outputs exactly $d_G(s,t)$.
--
--   $$
--   T_{\mathrm{pre}}\le T_{\mathrm{pre}}^{\mathrm{bound}},\qquad
--   \#\mathrm{written\ cells}+3+3m\le S,\qquad
--   T_{\mathrm{query}}(s,t)\le T_q,\qquad
--   \mathrm{answer}(s,t)=d_G(s,t).
--   $$
--
--   This is the published exact-oracle predicate of Theorem 1, with the parameter $k$ passed to both programs instead of the fixed value $0$. It is what lets one pair of programs realize a whole space–query trade-off: the parameter $\sigma$ of Theorem 2 is the input $k$.
--
--   **Formalization Note** The parameter occupies integer input cell 2 (one of the charged $3+3m$ input cells) and enters the word size $n+m+k+2$, so for $k\le n^2$ words still have $O(\log n)$ bits. Queries reset the registers and see only the stored memory and the two vertex indices. The file also records, as a definitional equality, that parameter $0$ gives back the published predicate.
-- source:
--   Eunjin Oh, Linear-Space Exact Distance Oracle for Minor-Free Graphs, STOC 2027 submission #160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/160.pdf, Theorem 2, PDF p.4 (printed p.2); model as in the published IsExactOracle (Theorem 1, same page)

import Mathlib
import Definitions.Def_TZLevelsADO_IsADO
import Definitions.Def_MinorFreeOracle_LinearSpace_ExactOracle

namespace MinorFreeOracle.LinearSpace.Supplement

/-- Oh, Theorem 2, PDF p.4 (printed p.2). The published deterministic exact-oracle predicate
`MinorFreeOracle.LinearSpace.IsExactOracle`, with the oracle parameter `k` supplied to both programs
instead of the fixed value `0`. The parameter sits in integer input cell 2 of the preprocessing run
(one of the `3 + 3m` charged input cells) and enters the word size `n + m + k + 2`. Preprocessing is
one halted run on the all-false tape within `Tpre` steps; its stored memory, counting the distinct
cells it writes plus the `3 + 3m` input cells, is at most `S`; from that same memory every query
pair `u, v` has a halted deterministic run within `Tq` steps whose real output is exactly
`d_G(u, v)`. -/
def IsExactOracleParam (Pre Qry : RealAPSP.Program) (G : TZLevelsADO.Graph) (k : ℕ)
    (Tpre S Tq : ℝ) : Prop :=
  ∃ t : ℕ,
    (TZLevelsADO.prepState Pre G k RealAPSP.zeroTape t).halted = true ∧
    (t : ℝ) ≤ Tpre ∧
    (((TZLevelsADO.cellsWritten Pre G k RealAPSP.zeroTape t).card +
      (3 + 3 * G.m) : ℕ) : ℝ) ≤ S ∧
    ∀ u v : Fin G.n, ∃ tq : ℕ,
      (TZLevelsADO.queryRun Qry G k
        (TZLevelsADO.prepState Pre G k RealAPSP.zeroTape t) u v tq).halted = true ∧
      (tq : ℝ) ≤ Tq ∧
      TZLevelsADO.answer (TZLevelsADO.queryRun Qry G k
        (TZLevelsADO.prepState Pre G k RealAPSP.zeroTape t) u v tq) =
        TZLevelsADO.dist G u v

/-- With parameter `0` the predicate is the published `IsExactOracle` of Theorem 1. -/
theorem isExactOracleParam_zero (Pre Qry : RealAPSP.Program) (G : TZLevelsADO.Graph)
    (Tpre S Tq : ℝ) :
    IsExactOracleParam Pre Qry G 0 Tpre S Tq =
      MinorFreeOracle.LinearSpace.IsExactOracle Pre Qry G Tpre S Tq := rfl

end MinorFreeOracle.LinearSpace.Supplement


