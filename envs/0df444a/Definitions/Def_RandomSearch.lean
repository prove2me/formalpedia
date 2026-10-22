-- Prove2me | Definitions.Def_RandomSearch
-- name    : RandomSearch
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-09T05:18:40.720245+00:00
-- url     : https://prove2.me/theorems/685179e8-f32e-4f88-b8a1-a44e141ba8ca
-- title:
--   Fixed-seed random search: predetermined query list and best-observed point
-- statement:
--   This module fixes the semantics of strategy 4 of the five-algorithm portfolio, *fixed-seed random search*: once the seed is frozen, the $N$ query points $q_1,\dots,q_N$ are completely determined by $(N, D)$ and the public sampling rule, and their positions do not depend on function values (source line 2183). The query list therefore enters as a parameter $q : \mathrm{Fin}\ N \to E$ given *before* the algorithm, and the output is the queried point at which the smallest value was observed, built by folding the strict-improvement step
--
--   $$b \mapsto \begin{cases} x, & o.\mathrm{value}(x) < o.\mathrm{value}(b), \\ b, & \text{otherwise},\end{cases}$$
--
--   where $o$ is a black-box oracle and $x$ ranges over the predetermined queries $q_0,\dots,q_{N-1}$. Because the comparison is strict, an earlier query is kept on a tie. The fold starts from *no best point yet*, which is reachable only at zero budget, exactly as in the frozen loop; the definitions `run` (the `Option`-valued fold) and `out` (its total form, resolving the impossible zero-budget case to the first query) record the two faces of the output. The frozen implementation's declared constants — sample box $8$, step $1/2$, seed $0$, span $16$ — are recorded as data, but nothing here uses the geometry of the sample box: every statement below holds for an arbitrary predetermined list, of which the seed-$0$ stream is one instance.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §21, strategy 4 (source line 2082), §24 (lines 2177-2183), §36.3; Lean: FullFormalization.RandomSearch lines 1-148

-- Generated from F:/20261008/FullFormalization\FullFormalization\RandomSearch.lean by skeleton subtraction (Phase 3-4):
-- every unselected declaration deleted, project imports rewritten.
/-
  FullFormalization.RandomSearch

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, section 21,
  strategy 4 (source line 2082): `fixed-seed random search`, and section 24
  (source lines 2177-2183):

      "固定 seed 后，random search 的 N 个查询点 q_1, ..., q_N 由 N, D 和公开采样
       规则完全确定，并且查询位置不依赖函数值。"

  Implementation semantics: `blackbox_algos.py`, `_random_search` and
  `_sample`:

      rng = random.Random(SAMPLE_SEED)           -- SAMPLE_SEED = 0
      for _ in range(spec.query_budget):
          point = (SAMPLE_STEP * rng.randint(-span, span) for each coordinate)
          answer = oracle.query(point)
          if best_value is None or answer["value"] < best_value:
              best_point, best_value = point, answer["value"]
      oracle.finish(best_point)

  with `SAMPLE_BOX = 8`, `SAMPLE_STEP = 1/2` and `span = int(SAMPLE_BOX /
  SAMPLE_STEP) = 16`.  The two facts that matter are:

  * the whole query list is fixed by the declared seed, the declared box and
    the declared step, hence by `(N, D)` alone — it does **not** depend on
    function values (source line 2183).  `q : Fin N → E` is therefore a
    parameter of this file, given before the function, and everything below is
    proved for *any* such fixed list.  This is the strict strengthening
    recorded in `DEPENDENCY_MAP.md` §9 D-2 and R11: the source uses only
    "fixed and independent of the function", and never any property of the
    concrete PRNG stream.  The seed-0 list of `blackbox_algos.py` is one
    instance.
  * the output is the **queried** point with the smallest observed value, and
    the comparison is strict (`<`), so on a tie the **earlier** query wins
    (`bestOf_pair_tie`).

  Nothing here uses the geometry of the sample box: the sample constants are
  recorded (`sampleBox`, `sampleStep`, `sampleSeed`, `sampleSpan`) because the
  frozen implementation declares them, but the theorems below hold for every
  predetermined query list.
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_PortfolioDefinitions

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*}

/-! ### The declared sampler constants (frozen implementation) -/











/-! ### The best observed point -/

/-- One comparison of the frozen loop: the new point replaces the incumbent
only on a **strict** improvement, so an earlier point is kept on a tie. -/
noncomputable def bestStep (o : Oracle E) : Option E → E → Option E
  | none, x => some x
  | some b, x => some (if o.value x < o.value b then x else b)

/-- The frozen loop's accumulator over a list of queries: start with "no best
point yet" and fold the strict-improvement comparison. -/
noncomputable def bestOf (o : Oracle E) : List E → Option E
  | [] => none
  | x :: xs => xs.foldl (bestStep o) (some x)





















/-! ### Strategy 4 on a predetermined query list -/

namespace RandomSearch



/-- The predetermined query list of strategy 4.  It is a parameter given
*before* the function (source lines 2177-2183); for the frozen implementation it
is the seed-0, box-`8`, step-`1/2` stream of `_random_search`. -/
noncomputable def queries {N : ℕ} (q : Fin N → E) : List E := List.ofFn q



/-- Strategy 4's output: the queried point with the smallest observed value.
`none` is possible only at zero budget, exactly as in the frozen loop. -/
noncomputable def run (o : Oracle E) {N : ℕ} (q : Fin N → E) : Option E :=
  bestOf o (queries q)



/-- At a nonempty budget the output is a genuine point: `out` is the frozen
`best_point`, with the (impossible, `0 < N`) `none` case resolved to the first
query so that the definition is total. -/
noncomputable def out (o : Oracle E) {N : ℕ} (q : Fin N → E) (hN : 0 < N) : E :=
  (run o q).getD (q ⟨0, hN⟩)

















end RandomSearch

end FullFormalization


