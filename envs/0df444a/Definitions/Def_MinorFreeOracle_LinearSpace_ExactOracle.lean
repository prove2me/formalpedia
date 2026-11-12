-- Prove2me | Definitions.Def_MinorFreeOracle_LinearSpace_ExactOracle
-- name    : MinorFreeOracle_LinearSpace_ExactOracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:42:55.568089+00:00
-- url     : https://prove2.me/theorems/f19429a7-ddcf-4e86-800b-ac02b2af63b4
-- title:
--   Deterministic exact distance oracles with charged input memory
-- statement:
--   Let Pre and Qry be finite comparison–addition word-RAM programs, and let G be a weighted graph. The predicate requires one halted preprocessing run on the all-false tape within time T_pre. Its stored memory costs at most S cells, counting distinct cells written by preprocessing plus all 3+3m input cells, where m is the number of edges. From that same stored memory, every query pair s,t must have a halted deterministic query run within T_q steps whose real output is exactly d_G(s,t).
--
--   $$
--   T_{\mathrm{pre}}\le T_{\mathrm{pre}}^{\mathrm{bound}},\quad
--   \#\mathrm{written\ cells}+3+3m\le S,\quad
--   T_{\mathrm{query}}(s,t)\le T_q,\quad
--   \mathrm{answer}(s,t)=d_G(s,t).
--   $$
--
--   The predicate constrains actual program runs; it does not assume a correct oracle as input. Each query resets the registers and supplies the two vertex indices while retaining preprocessing memory. The programs use logarithmic integer words and only real addition, negation and comparison. The goal applies this predicate only to connected nonnegatively weighted graphs, where real shortest-path distance is finite and attained.
-- source:
--   Eunjin Oh, Linear-Space Exact Distance Oracle for Minor-Free Graphs, STOC 2027 submission #160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/160.pdf, Theorem 1, PDF p.4 (printed p.2); §1, PDF pp.3–5; §3, PDF p.15; computational model and memory-layout reading

import Mathlib
import Definitions.Def_TZLevelsADO_IsADO

namespace MinorFreeOracle.LinearSpace

/-- Oh, Theorem 1, PDF p.4 (printed p.2). Deterministic preprocessing and queries on the
comparison–addition word RAM. Input cells are charged in addition to all preprocessing writes.
Each query starts afresh from the stored preprocessing memory; only its two vertex inputs change.
This predicate asserts bounds on actual program runs, rather than packaging bounds in an oracle. -/
def IsExactOracle (Pre Qry : RealAPSP.Program) (G : TZLevelsADO.Graph)
    (Tpre S Tq : ℝ) : Prop :=
  ∃ t : ℕ,
    (TZLevelsADO.prepState Pre G 0 RealAPSP.zeroTape t).halted = true ∧
    (t : ℝ) ≤ Tpre ∧
    (((TZLevelsADO.cellsWritten Pre G 0 RealAPSP.zeroTape t).card +
      (3 + 3 * G.m) : ℕ) : ℝ) ≤ S ∧
    ∀ u v : Fin G.n, ∃ tq : ℕ,
      (TZLevelsADO.queryRun Qry G 0
        (TZLevelsADO.prepState Pre G 0 RealAPSP.zeroTape t) u v tq).halted = true ∧
      (tq : ℝ) ≤ Tq ∧
      TZLevelsADO.answer (TZLevelsADO.queryRun Qry G 0
        (TZLevelsADO.prepState Pre G 0 RealAPSP.zeroTape t) u v tq) =
        TZLevelsADO.dist G u v

end MinorFreeOracle.LinearSpace


