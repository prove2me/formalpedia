-- Prove2me | Definitions.Def_BCFGJPSSV26_FL_Main
-- name    : BCFGJPSSV26_FL_Main
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:17:43.645284+00:00
-- url     : https://prove2.me/theorems/c45c753b-ba17-4705-88bf-1dff705d4b91
-- title:
--   BCFGJPSSV26.FL.Main — Theorem 1.4
-- statement:
--   This is module `BCFGJPSSV26.FL.Main` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26a, Theorem 1.4] (Theorem 4.3 in full): `BCFGJPSSV26.FL.fl_main` proves the statement
--   `BCFGJPSSV26.FL.Thm14` of `BCFGJPSSV26.facilityLocation_lmp`, a polynomial-time `1.9499`-LMP
--   algorithm for uncapacitated facility location. The algorithm is `BCFGJPSSV26.FL.alg` on the tuple of
--   the instance and the opening cost (`FL/Algorithm.lean`): the greedy algorithm of [BCFGJPSSV26a,
--   Section 5], with exact tests, run once by CompleteSolution on a scaled instance, or the trivial
--   solution, whichever has the smaller objective `cost S + 1.9499 f |S|`. It runs in polynomial time
--   (`BCFGJPSSV26.FL.alg_polytime`) and satisfies the guarantee (`BCFGJPSSV26.FL.alg_spec`).
--
--   The proof of the guarantee (`BCFGJPSSV26.FL.alg_spec`), for an optimal set `O`
--   (`BCFGJPSSV26.FL.exists_optFL`):
--
--   * if the trivial solution has at most `|O|` facilities, or `f = 0`, it meets the bound
--     (`BCFGJPSSV26.FL.score_trivialSol_le`);
--   * otherwise `n ≥ 2`, `m ≥ 2`, `f > 0`, and `O` has a positive cost
--     (`BCFGJPSSV26.FL.trivialSol_length_le_card`), so the greedy run meets the bound
--     (`BCFGJPSSV26.FL.runFL_spec`, from the robust LMP guarantee
--     `BCFGJPSSV26.Greedy.robust_lmp` of Theorem 1.2's analysis);
--   * the output has the smaller objective of the two (`BCFGJPSSV26.FL.alg_spec_of`).
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.FL.alg_spec`, `BCFGJPSSV26.FL.fl_main` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_FL_Main`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/FL/Main.lean

module

public import Definitions.Def_BCFGJPSSV26_FL_Run
public import Definitions.Def_BCFGJPSSV26_FL_PolyTime

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.FL.Main` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Theorem 1.4

[BCFGJPSSV26a, Theorem 1.4] (Theorem 4.3 in full): `BCFGJPSSV26.FL.fl_main` proves the statement
`BCFGJPSSV26.FL.Thm14` of `BCFGJPSSV26.facilityLocation_lmp`, a polynomial-time `1.9499`-LMP
algorithm for uncapacitated facility location. The algorithm is `BCFGJPSSV26.FL.alg` on the tuple of
the instance and the opening cost (`FL/Algorithm.lean`): the greedy algorithm of [BCFGJPSSV26a,
Section 5], with exact tests, run once by CompleteSolution on a scaled instance, or the trivial
solution, whichever has the smaller objective `cost S + 1.9499 f |S|`. It runs in polynomial time
(`BCFGJPSSV26.FL.alg_polytime`) and satisfies the guarantee (`BCFGJPSSV26.FL.alg_spec`).

The proof of the guarantee (`BCFGJPSSV26.FL.alg_spec`), for an optimal set `O`
(`BCFGJPSSV26.FL.exists_optFL`):

* if the trivial solution has at most `|O|` facilities, or `f = 0`, it meets the bound
  (`BCFGJPSSV26.FL.score_trivialSol_le`);
* otherwise `n ≥ 2`, `m ≥ 2`, `f > 0`, and `O` has a positive cost
  (`BCFGJPSSV26.FL.trivialSol_length_le_card`), so the greedy run meets the bound
  (`BCFGJPSSV26.FL.runFL_spec`, from the robust LMP guarantee
  `BCFGJPSSV26.Greedy.robust_lmp` of Theorem 1.2's analysis);
* the output has the smaller objective of the two (`BCFGJPSSV26.FL.alg_spec_of`).
-/

@[expose] public section

namespace BCFGJPSSV26.FL

open Encoding

variable {I : Instance}

/-- The statement of **Theorem 1.4** (`BCFGJPSSV26.facilityLocation_lmp`). -/
def Thm14 : Prop :=
    ∃ A : Instance × ℚ → List ℕ,
      Turing.MultiTapeTM.ComputableInPolyTime A (encPair encInstance encRat) encCenters ∧
      ∀ I : Instance, I.Valid → 0 < I.n → ∀ f : ℚ, 0 ≤ f →
        I.IsCenterList (A (I, f)) ∧
        I.cost (I.centers (A (I, f))) ≤
          1.9499 * (I.optFL (f : ℝ) - (f : ℝ) * (A (I, f)).length)

end BCFGJPSSV26.FL


