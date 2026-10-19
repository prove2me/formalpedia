-- Prove2me | Definitions.Def_MIPRE_Foundations_Repeat_Sampler
-- name    : MIPRE_Foundations_Repeat_Sampler
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T14:38:25.720347+00:00
-- url     : https://prove2.me/theorems/062cb9d5-5836-4f83-ab6d-bcde0894cf29
-- title:
--   Definitions of Sampler: The program of the repeated sampler The sampler of `ComputeParrepVerifier` (`thm:parallel-repetition`;…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Repeat.Sampler` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The program of the repeated sampler. The sampler of `ComputeParrepVerifier` (`thm:parallel-repetition`; `planning/repetition-verifier.md`, R3(b)) as a program of the ambient model. It is one fixed program `repSampCore univ` — `univ` a universal machine — run through the s-m-n construction `hardcode` on the datum `(S̄, λ, τ)`: its input is then `((S̄, λ, τ), (n, q))`, with `S̄` the input sampler's program, `λ, τ` in binary and `q` a query. It 1. asks `S̄` for its dimension `s = s(n)`, through `univ`; 2. on the dimension query (`kind = 0`, i.e. `nil`) runs `dimProg`: the numeral `2^m s` with `m…
--
--   **Definitions** (10): `MIPRE.Cost.Prog.coreDispatch` (The dispatch on the kind of the query, in the environment `coreEnv`: `dimProg` on `(s, λ, n, τ)` when the kind is `nil`, `lockProg` on…); `MIPRE.Cost.Prog.coreEnv` (The environment of the dispatch: the dimension `sz`, the dimension query, `n`, the query `d`, `λ`, `τ`, `S̄`, and the input's spine.); `MIPRE.Cost.Prog.dimCost` (The cost of `dimProg` with exponent `tau`, lists of lengths `L` and sizes `Λ + N`, and a numeral of size `Ssz`.); `MIPRE.Cost.Prog.dimProg` (On `(s, λ, n, τ)` — `s` in binary and nonzero, `λ, n` bit lists, `τ` in binary — the bits of `2^{τ (|λ| + |n|)} s`; `nil` when `s` is `nil`.); `MIPRE.Cost.Prog.lockCost` (The cost of `lockProg` at dimension `s`, context pieces of total size `C`, vectors of sizes `U, Y`, and a bound `Z` on the sizes in the…); `MIPRE.Cost.Prog.lockInput` (The input of `lockProg`.); `MIPRE.Cost.Prog.lockProg` (On `(S̄, n, s, kind, w, j, u, y)` — `s` in binary — the concatenation of the answers of `S̄` on the blocks of `u` and `y`, through `univ`;…); `MIPRE.Cost.Prog.repSampCore` (The core of the repeated sampler, before the s-m-n construction: on `((S̄, λ, τ), (n, q))`, the dimension of `S̄` at `n` through `univ`,…); `MIPRE.Cost.Prog.sampParams` (The hardcoded datum `(S̄, λ, τ)`.); `MIPRE.Cost.Prog.toUnaryCost` (The cost of converting a numeral to unary (`toUnaryProg_runs`).).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Repeat.Sampler` (`MIPRE/Foundations/Repeat/Sampler.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 20 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/Sampler.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Sampler.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B

/-!
# The program of the repeated sampler

The sampler of `ComputeParrepVerifier` (`thm:parallel-repetition`;
`planning/repetition-verifier.md`, R3(b)) as a program of the ambient model. It is one fixed
program `repSampCore univ` — `univ` a universal machine — run through the s-m-n construction
`hardcode` on the datum `(S̄, λ, τ)`: its input is then `((S̄, λ, τ), (n, q))`, with `S̄` the
input sampler's program, `λ, τ` in binary and `q` a query. It

1. asks `S̄` for its dimension `s = s(n)`, through `univ`;
2. on the dimension query (`kind = 0`, i.e. `nil`) runs `dimProg`: the numeral `2^m s` with
   `m = τ (|λ| + |n|)`, written as `m` zero bits in front of the bits of `s` (`powBody`);
3. on any other query `(kind, w, j, u, y)` runs `lockProg`: `s` in unary, then the block loop
   `mapBody` over `u` and `y` in blocks of `s`, and the concatenation of the answers.

Every input of the form `((S̄, λ, τ), (n, d))` halts: the missing components of a malformed
`d` are `nil`, on which each `elim` stops with `nil`. The costs are explicit throughout, for
the time bound of the repeated verifier (`MIPRE.Foundations.Repeat.SamplerCost`).
-/

namespace MIPRE.Cost

open Data

namespace Prog

/-! ## The dimension branch -/

/-- On `(s, λ, n, τ)` — `s` in binary and nonzero, `λ, n` bit lists, `τ` in binary — the bits
of `2^{τ (|λ| + |n|)} s`; `nil` when `s` is `nil`. -/
def dimProg : Prog :=
  .elim 0 .nil
    (.elim 0 .nil
      (.elim 3 .nil
        (.elim 1 .nil
          (.let_ (callVar 1 toUnaryProg)
            (.let_ (.cons (.var 0) (.cons (.var 3) (.cons (.var 1) (.var 7))))
              (.loop powBody))))))

/-- The cost of converting a numeral to unary (`toUnaryProg_runs`). -/
def toUnaryCost (n : ℕ) : ℕ :=
  (Nat.size n + 2) * ((n + 1) * (4 * n + 14) + 7 * esize n + 8 * n + 90)

/-- The cost of `dimProg` with exponent `tau`, lists of lengths `L` and sizes `Λ + N`, and a
numeral of size `Ssz`. -/
def dimCost (tau L Λ N Ssz : ℕ) : ℕ :=
  toUnaryCost tau + esize tau + powCost tau L (Λ + N + Ssz) + 2 * tau + Λ + N + Ssz + 20

/-! ## The block branch -/

/-- On `(S̄, n, s, kind, w, j, u, y)` — `s` in binary — the concatenation of the answers of
`S̄` on the blocks of `u` and `y`, through `univ`; `nil` when `s = 0`. -/
def lockProg (univ : Prog) : Prog :=
  .elim 0 .nil
    (.elim 1 .nil
      (.elim 1 .nil
        (.elim 1 .nil
          (.elim 1 .nil
            (.elim 1 .nil
              (.elim 1 .nil
                (.let_ (callVar 8 toUnaryProg)
                  (.elim 0 .nil
                    (.let_ (.cons (.var 15) (.cons (.var 13) (.cons (.var 9)
                        (.cons (.var 7) (.var 5)))))
                      (.let_ (.cons (.var 3) (.cons (.var 4) (.cons (.var 5) (.cons (.var 0) .nil))))
                        (.let_ (.loop (mapBody univ))
                          (callVar 0 revProg))))))))))))

/-- The input of `lockProg`. -/
def lockInput (sD nD sz kD wD jD uD yD : Data) : Data :=
  .cons sD (.cons nD (.cons sz (.cons kD (.cons wD (.cons jD (.cons uD yD))))))

/-- The cost of `lockProg` at dimension `s`, context pieces of total size `C`, vectors of
sizes `U, Y`, and a bound `Z` on the sizes in the loop. -/
def lockCost (s C U Y Z : ℕ) : ℕ :=
  esize s + toUnaryCost s + 4 * C + 4 * s + 4 * U + 4 * Y + (U + 1) * mapIter Z +
    (Z + 2) * (Z + 13) + 3 * Z + 60

/-! ## The core program -/

/-- The dispatch on the kind of the query, in the environment `coreEnv`: `dimProg` on
`(s, λ, n, τ)` when the kind is `nil`, `lockProg` on `(S̄, n, s, kind, rest)` otherwise. -/
def coreDispatch (univ : Prog) : Prog :=
  .elim 3 .nil
    (.elim 0
      (.let_ (.cons (.var 2) (.cons (.var 6) (.cons (.var 4) (.var 7)))) (callVar 0 dimProg))
      (.let_ (.cons (.var 10) (.cons (.var 6) (.cons (.var 4) (.cons (.var 2) (.var 3)))))
        (callVar 0 (lockProg univ))))

/-- The core of the repeated sampler, before the s-m-n construction: on
`((S̄, λ, τ), (n, q))`, the dimension of `S̄` at `n` through `univ`, then the dispatch. -/
def repSampCore (univ : Prog) : Prog :=
  .elim 0 .nil
    (.elim 0 .nil
      (.elim 1 .nil
        (.elim 5 .nil
          (.let_ (.cons (.var 4) (.cons (.var 0) (.const (encode CL.Sampler.Query.dimension))))
            (.let_ (callVar 0 univ) (coreDispatch univ))))))

/-- The hardcoded datum `(S̄, λ, τ)`. -/
def sampParams (sD lD tD : Data) : Data := .cons sD (.cons lD tD)

/-- The environment of the dispatch: the dimension `sz`, the dimension query, `n`, the query
`d`, `λ`, `τ`, `S̄`, and the input's spine. -/
def coreEnv (sD lD tD nD d sz : Data) : Env :=
  [sz, .cons sD (.cons nD (encode CL.Sampler.Query.dimension)), nD, d, lD, tD, sD,
    .cons lD tD, sampParams sD lD tD, .cons nD d, .cons (sampParams sD lD tD) (.cons nD d)]

end Prog

end MIPRE.Cost


