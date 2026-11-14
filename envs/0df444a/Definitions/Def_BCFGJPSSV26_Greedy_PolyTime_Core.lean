-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Core
-- name    : BCFGJPSSV26_Greedy_PolyTime_Core
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:16:18.676638+00:00
-- url     : https://prove2.me/theorems/fca21852-f4e3-4e0d-8e75-899f27a4c70b
-- title:
--   BCFGJPSSV26.Greedy.PolyTime.Core — The core runs in polynomial time
-- statement:
--   This is module `BCFGJPSSV26.Greedy.PolyTime.Core` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   `BCFGJPSSV26.Greedy.core_polytime`: for fixed constants, the core of `Greedy/Alg/Defs.lean` is
--   computable in polynomial time, on core inputs encoded as instances are (`BCFGJPSSV26.encRaw`) except
--   that the numbers `n` of clients and `m` of facilities are written in unary
--   (`BCFGJPSSV26.Greedy.encCoreIn`): the core loops over all clients and all facilities, and runs
--   CompleteSequence `L = m + 4` times, so `n` and `m` must be polynomial in the length of the input.
--   For an instance they are (its table has `n + m` rows), and `BCFGJPSSV26.Greedy.toRawU_polytime`
--   converts. This does not need any correctness property of the algorithm: every loop has a count
--   polynomial in the input (`L` steps of CompleteSequence, `2R` sequences and phases, `Pf` and `Pu`
--   steps of the searches, `L` rounds of the walk, each with at most `|cur|` deletions), and every
--   number is a rational of polynomially many bits (`θ r = (1 + ε²)^r` for `r ≤ R`, the grids, the
--   profiles, and the sums of `n` such terms in the tests, computed with a common denominator as in
--   `Background/PolyTime/Rat.lean`). Here `R = O(log(n M) / ε²)` and `Pf, Pu = O(R + log n)` for fixed
--   `ε`, so all counts are polynomial in the length of the input.
--
--   The proof is in the files `Greedy/PolyTime/Aux*.lean`, namespace `BCFGJPSSV26.Greedy.PT`:
--
--   * `AuxBasic`: the encodings (atoms and sequences in binary), generic certificates (powers,
--     ceilings, `⌈log₂⌉` in unary, folds of `min` and `max`) and bounds on encoded lengths;
--   * `AuxCtx`: the parameters (`BCFGJPSSV26.Greedy.ipar`), profiles and tests;
--   * `AuxComplete`: CompleteSequence (at most one atom per step) and CompleteSolution (at most one
--     sequence of at most `L` atoms per step);
--   * `AuxSearch`: pairs and results as tagged tuples, the binary searches (their states stay below
--     the initial upper end) and the bisection;
--   * `AuxWalk`, `AuxRound`: the kinds of the points of the walk as tagged tuples, and the walk (every
--     recorded sequence has at most `|H'p| + 2L + 1` atoms, there are at most `1 + L (|H'p| + 2L + 2)`
--     points, and every atom comes from the inputs, the completions or the free copies);
--   * `AuxMerge`: BinSearch, step C, the dispatch of step B, the phases;
--   * `AuxCore`: the invariant of the merge loop (`BCFGJPSSV26.Greedy.PT.ResOK`: at most `2R`
--     sequences of at most `9L + 5` atoms, the sequences from the current phase on with at most `L`
--     atoms, facilities at most `m` and offset indices at most `2^Pu + 1`), which bounds its states,
--     and the certificate of the core.
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Greedy.core_polytime` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Core`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/PolyTime/Core.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Defs
public import Definitions.Def_BCFGJPSSV26_Basic_Raw
public import Definitions.Def_BuhaiPapers_Background_PolyTime_Rat
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxCore

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.PolyTime.Core` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The core runs in polynomial time

`BCFGJPSSV26.Greedy.core_polytime`: for fixed constants, the core of `Greedy/Alg/Defs.lean` is
computable in polynomial time, on core inputs encoded as instances are (`BCFGJPSSV26.encRaw`) except
that the numbers `n` of clients and `m` of facilities are written in unary
(`BCFGJPSSV26.Greedy.encCoreIn`): the core loops over all clients and all facilities, and runs
CompleteSequence `L = m + 4` times, so `n` and `m` must be polynomial in the length of the input.
For an instance they are (its table has `n + m` rows), and `BCFGJPSSV26.Greedy.toRawU_polytime`
converts. This does not need any correctness property of the algorithm: every loop has a count
polynomial in the input (`L` steps of CompleteSequence, `2R` sequences and phases, `Pf` and `Pu`
steps of the searches, `L` rounds of the walk, each with at most `|cur|` deletions), and every
number is a rational of polynomially many bits (`θ r = (1 + ε²)^r` for `r ≤ R`, the grids, the
profiles, and the sums of `n` such terms in the tests, computed with a common denominator as in
`Background/PolyTime/Rat.lean`). Here `R = O(log(n M) / ε²)` and `Pf, Pu = O(R + log n)` for fixed
`ε`, so all counts are polynomial in the length of the input.

The proof is in the files `Greedy/PolyTime/Aux*.lean`, namespace `BCFGJPSSV26.Greedy.PT`:

* `AuxBasic`: the encodings (atoms and sequences in binary), generic certificates (powers,
  ceilings, `⌈log₂⌉` in unary, folds of `min` and `max`) and bounds on encoded lengths;
* `AuxCtx`: the parameters (`BCFGJPSSV26.Greedy.ipar`), profiles and tests;
* `AuxComplete`: CompleteSequence (at most one atom per step) and CompleteSolution (at most one
  sequence of at most `L` atoms per step);
* `AuxSearch`: pairs and results as tagged tuples, the binary searches (their states stay below
  the initial upper end) and the bisection;
* `AuxWalk`, `AuxRound`: the kinds of the points of the walk as tagged tuples, and the walk (every
  recorded sequence has at most `|H'p| + 2L + 1` atoms, there are at most `1 + L (|H'p| + 2L + 2)`
  points, and every atom comes from the inputs, the completions or the free copies);
* `AuxMerge`: BinSearch, step C, the dispatch of step B, the phases;
* `AuxCore`: the invariant of the merge loop (`BCFGJPSSV26.Greedy.PT.ResOK`: at most `2R`
  sequences of at most `9L + 5` atoms, the sequences from the current phase on with at most `L`
  atoms, facilities at most `m` and offset indices at most `2^Pu + 1`), which bounds its states,
  and the certificate of the core.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Turing.MultiTapeTM

/-- **Core inputs** encoded as instances are, except that `n` and `m` are in unary. -/
abbrev encCoreIn : CoreIn ↪ List Bool := PT.encCI

end BCFGJPSSV26.Greedy


