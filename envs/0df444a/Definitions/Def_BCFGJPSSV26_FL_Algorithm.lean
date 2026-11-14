-- Prove2me | Definitions.Def_BCFGJPSSV26_FL_Algorithm
-- name    : BCFGJPSSV26_FL_Algorithm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:59:47.682763+00:00
-- url     : https://prove2.me/theorems/47018bcf-e672-449b-b440-e25144b7c204
-- title:
--   BCFGJPSSV26.FL.Algorithm — The algorithm of Theorem 1.4
-- statement:
--   This is module `BCFGJPSSV26.FL.Algorithm` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26a, Theorem 1.4] (Theorem 4.3 in full): an LMP algorithm for uncapacitated facility
--   location with opening cost `f`, with the factor `λ = 1.9499` (`BCFGJPSSV26.FL.lmpC`). It reuses
--   the greedy algorithm of [BCFGJPSSV26a, Section 5] (`Greedy/Alg/Defs.lean`): CompleteSolution
--   (`BCFGJPSSV26.Greedy.Ctx.complete`) from the empty solution, with the exact tests of
--   `Greedy/Openable.lean`. Facility location needs neither the bisection on the opening cost nor the
--   merge.
--
--   On the tuple `x = (n, m, k, table)` of an instance and the opening cost `f`:
--
--   * **Scale** (`BCFGJPSSV26.FL.tFL`): `t = min (d_min / (10⁵ n), f)`, where `d_min` is the least
--     positive client–facility distance (`BCFGJPSSV26.FL.dminFL`). The client–facility distances
--     become `d(j, i) / t + 1 ≥ 1` (`BCFGJPSSV26.FL.stabFL`); on the whole space this is the
--     pseudometric `d / t + 1` off the diagonal. Every client pays `1` more, `n` in all, which costs
--     `n t ≤ d_min / 10⁵` after scaling back.
--   * **Parameters** (`BCFGJPSSV26.FL.iparFL`): those of `BCFGJPSSV26.Greedy.ipar` with
--     `δ = 10⁻⁶` (`BCFGJPSSV26.FL.δ0`), the paper's `ε = δ / 10`, the scaled opening cost
--     `f̂ = λ (1 - δ) f / t` (`BCFGJPSSV26.FL.fhatFL`), and the bound
--     `M = d_max / t + 1 + f̂` on the scaled distances and on `f̂` (`BCFGJPSSV26.FL.MFL`), from which
--     the number `R` of phases is computed as in `BCFGJPSSV26.Greedy.Rof`.
--   * **The greedy run** (`BCFGJPSSV26.FL.runFL`): the facilities of CompleteSolution at `f̂`.
--   * **The output** (`BCFGJPSSV26.FL.alg`): the run if it is a list of distinct facilities with a
--     smaller `cost S + λ f |S|` (`BCFGJPSSV26.FL.score`) than the trivial solution
--     (`BCFGJPSSV26.Greedy.trivialSol`, the nearest facility of every client), and the trivial
--     solution otherwise. The trivial solution serves when `n = 1`, `m = 1`, `f = 0`, or when an
--     optimal set costs `0`.
--
--   **Contents.** The module is published as a whole: 17 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_FL_Algorithm`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/FL/Algorithm.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Defs
public import Definitions.Def_BCFGJPSSV26_Greedy_Reduction_Scale

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.FL.Algorithm` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The algorithm of Theorem 1.4

[BCFGJPSSV26a, Theorem 1.4] (Theorem 4.3 in full): an LMP algorithm for uncapacitated facility
location with opening cost `f`, with the factor `λ = 1.9499` (`BCFGJPSSV26.FL.lmpC`). It reuses
the greedy algorithm of [BCFGJPSSV26a, Section 5] (`Greedy/Alg/Defs.lean`): CompleteSolution
(`BCFGJPSSV26.Greedy.Ctx.complete`) from the empty solution, with the exact tests of
`Greedy/Openable.lean`. Facility location needs neither the bisection on the opening cost nor the
merge.

On the tuple `x = (n, m, k, table)` of an instance and the opening cost `f`:

* **Scale** (`BCFGJPSSV26.FL.tFL`): `t = min (d_min / (10⁵ n), f)`, where `d_min` is the least
  positive client–facility distance (`BCFGJPSSV26.FL.dminFL`). The client–facility distances
  become `d(j, i) / t + 1 ≥ 1` (`BCFGJPSSV26.FL.stabFL`); on the whole space this is the
  pseudometric `d / t + 1` off the diagonal. Every client pays `1` more, `n` in all, which costs
  `n t ≤ d_min / 10⁵` after scaling back.
* **Parameters** (`BCFGJPSSV26.FL.iparFL`): those of `BCFGJPSSV26.Greedy.ipar` with
  `δ = 10⁻⁶` (`BCFGJPSSV26.FL.δ0`), the paper's `ε = δ / 10`, the scaled opening cost
  `f̂ = λ (1 - δ) f / t` (`BCFGJPSSV26.FL.fhatFL`), and the bound
  `M = d_max / t + 1 + f̂` on the scaled distances and on `f̂` (`BCFGJPSSV26.FL.MFL`), from which
  the number `R` of phases is computed as in `BCFGJPSSV26.Greedy.Rof`.
* **The greedy run** (`BCFGJPSSV26.FL.runFL`): the facilities of CompleteSolution at `f̂`.
* **The output** (`BCFGJPSSV26.FL.alg`): the run if it is a list of distinct facilities with a
  smaller `cost S + λ f |S|` (`BCFGJPSSV26.FL.score`) than the trivial solution
  (`BCFGJPSSV26.Greedy.trivialSol`, the nearest facility of every client), and the trivial
  solution otherwise. The trivial solution serves when `n = 1`, `m = 1`, `f = 0`, or when an
  optimal set costs `0`.
-/

@[expose] public section

namespace BCFGJPSSV26.FL

open Greedy

/-! ### Constants -/

/-- The LMP factor `λ = 1.9499`. -/
def lmpC : ℚ := 19499 / 10000

/-- The constant `δ = 10⁻⁶` of the greedy algorithm. -/
def δ0 : ℚ := 1 / 1000000

/-- The paper's `ε = δ / 10`. -/
def ε0 : ℚ := δ0 / 10

/-- The factor `10⁵` of the scale. -/
def cS : ℚ := 100000

/-! ### Scaling -/

/-- The least positive client–facility distance (`0` if there is none). -/
def dminFL (x : Raw) : ℚ := Combine.minQ (guesses x)

/-- The scale `t = min (d_min / (10⁵ n), f)`. -/
def tFL (x : Raw) (f : ℚ) : ℚ := min (dminFL x / (cS * x.n)) f

/-- The scaled opening cost `f̂ = λ (1 - δ) f / t`. -/
def fhatFL (x : Raw) (f : ℚ) : ℚ := lmpC * (1 - δ0) * f / tFL x f

/-- The scaled table: `n` rows of the `m` client–facility distances `d(j, i) / t + 1`. -/
def stabFL (x : Raw) (f : ℚ) : List (List ℚ) :=
  (List.range x.n).map fun j ↦ (List.range x.m).map fun i ↦ x.fdist j i / tFL x f + 1

/-- The bound `M = d_max / t + 1 + f̂` on the scaled distances and on `f̂`. -/
def MFL (x : Raw) (f : ℚ) : ℚ := x.dMaxQ / tFL x f + 1 + fhatFL x f

/-- The slack `η = δ² / (100 n²)` of `BCFGJPSSV26.Greedy.ipar` (unused by CompleteSolution). -/
def ηFL (n : ℕ) : ℚ := δ0 ^ 2 / (100 * (n : ℚ) ^ 2)

/-- The number of phases: `R = ⌈1/ε²⌉ ⌈log₂ ⌈5 n M⌉⌉ + 1`. -/
def RFL (x : Raw) (f : ℚ) : ℕ := ⌈1 / ε0 ^ 2⌉₊ * Nat.clog 2 ⌈5 * (x.n : ℚ) * MFL x f⌉₊ + 1

/-- The cap of the profiles: `K = 2 θ R`. -/
def KFL (x : Raw) (f : ℚ) : ℚ := 2 * (1 + ε0 ^ 2) ^ RFL x f

/-- The parameters of the greedy run: those of `BCFGJPSSV26.Greedy.ipar` with the bound `M` of
`BCFGJPSSV26.FL.MFL` and `k = 1` (the number `k` plays no role in CompleteSolution). -/
def iparFL (x : Raw) (f : ℚ) : IPar where
  n := x.n
  m := x.m
  k := 1
  δ := δ0
  ε := ε0
  M := MFL x f
  η := ηFL x.n
  K := KFL x f
  fmin := δ0
  fmax := 4 * (x.n : ℚ) * MFL x f
  R := RFL x f
  Pf := Nat.clog 2 ⌈4 * (x.n : ℚ) * MFL x f / ηFL x.n⌉₊
  Pu := Nat.clog 2 ⌈KFL x f / ηFL x.n⌉₊
  L := x.m + 4

/-- The context of the greedy run: its parameters and the scaled table. -/
def ctxFL (x : Raw) (f : ℚ) : Ctx := ⟨iparFL x f, stabFL x f⟩

/-! ### The algorithm -/

/-- **The greedy run**: the facilities of CompleteSolution from the empty solution, at the
scaled opening cost `f̂`. -/
def runFL (x : Raw) (f : ℚ) : List ℕ := toCenters ((ctxFL x f).complete (fhatFL x f) [])

/-- The objective `cost S + λ f |S|` of a list of facilities, computed exactly. -/
def score (x : Raw) (f : ℚ) (S : List ℕ) : ℚ := x.cost S + lmpC * f * S.length

/-- **The algorithm of Theorem 1.4**: the greedy run if it is a list of distinct facilities with
a smaller objective than the trivial solution, and the trivial solution otherwise. -/
def alg (x : Raw) (f : ℚ) : List ℕ :=
  if Combine.valid x.m x.m (runFL x f) &&
      decide (score x f (runFL x f) < score x f (trivialSol x)) then runFL x f
  else trivialSol x

end BCFGJPSSV26.FL


