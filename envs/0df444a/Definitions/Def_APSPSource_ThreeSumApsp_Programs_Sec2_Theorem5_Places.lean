-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Places
-- name    : APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Places
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:27:36.02754+00:00
-- url     : https://prove2.me/theorems/755bec57-c1fe-4651-a96b-316b303e4cd8
-- title:
--   Parameters and memory layout for shared algebraic preprocessing
-- statement:
--   The parameter record stores $L$ levels, $m$ inner levels, and the outer matrix size $N$. It defines
--
--   $$D=4^m,\quad N_0=3^{L-m},\quad K=\binom Lm,\quad K_0=\lfloor\sqrt K\rfloor,\quad K_K=K_0^2,$$
--
--   along with the number of row and column bands, encoding length $10^L$, and input-array length $7^L$.
--
--   Starting at address $b_0$, consecutive memory regions hold a directory of 32 cells; tables of powers of three, four, seven, and ten; Pascal-row scratch space; two coefficient tables of 70 cells each; subset masks; row-band and block indices; base-three and base-four digit tables; all band encodings; an input-array buffer; and recursive-encoding scratch space. Each address is the previous region's endpoint.
--
--   The directory list records the first 31 parameter and address cells, including the first free address after these regions. This supplies the fixed layout used by the shared preprocessing routines.
--
--   References:
--
--   1. [Source formalization, lines 34–42](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Places.lean#L34-L42).
--   2. [Source formalization, lines 46–59](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Places.lean#L46-L59).
--   3. [Source formalization, lines 62–65](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Places.lean#L62-L65).
--   4. [Source formalization, lines 69–109](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Places.lean#L69-L109).
--   5. [Source formalization, lines 113–118](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Places.lean#L113-L118).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Places.lean#L34-L42; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Places.lean#L46-L59; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Places.lean#L62-L65; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Places.lean#L69-L109; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Places.lean#L113-L118

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Tiling_Definitions
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Theorem 5 in the light language: sizes and places

The sizes of the tables and arrays of Theorem 5's program, and their places in the memory. No
program occurs here.

The program for Theorem 5 (the solver) and the data structure of Section 4 begin with the same
stage, the shared stage, which fills the shared block: a directory of 32 cells with the sizes and
the addresses of the areas (`dirList`), then the tables, then the encodings of all bands, then two
scratch areas. The solver has a private block behind it. The areas lie one after the other:
`Par.places` (the shared block) and `Par.places5` (the private block) say where every area begins
and ends. `Par.sizes` collects the inequalities between the sizes, each of which has a name of its
own.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## Sizes -/

/-- The parameters of the recursion and of the matrices: `L` levels, `m` of them inner, matrices
`N × D` and `D × N` with `D = 4^m`. -/
structure Par where
  /-- The number of levels of the recursion. -/
  L : ℕ
  /-- The number of inner levels. -/
  m : ℕ
  /-- The number of rows of `X` and of columns of `Y`. -/
  N : ℕ

namespace Par

/-- `D = 4^m`. -/
def D (p : Par) : ℕ := ThreeSumApsp.D p.m
/-- The number `L - m` of outer levels. -/
def Lo (p : Par) : ℕ := p.L - p.m
/-- `N₀ = 3^{L-m}`. -/
def N0 (p : Par) : ℕ := ThreeSumApsp.N0 p.L p.m
/-- `K = binom(L, m)`. -/
def K (p : Par) : ℕ := ThreeSumApsp.K p.L p.m
/-- `K₀ = ⌊√K⌋`. -/
def K0 (p : Par) : ℕ := ThreeSumApsp.K0 p.L p.m
/-- The number `K₀²` of subsets in the table. -/
def KK (p : Par) : ℕ := p.K0 * p.K0
/-- The number of row bands, and of column bands. -/
def nB (p : Par) : ℕ := numBands p.L p.m p.N


/-- The number `10^L` of leaves: the length of an encoding. -/
def T (p : Par) : ℕ := 10 ^ p.L
/-- The number `7^L` of left strings: the length of an input array. -/
def S7 (p : Par) : ℕ := 7 ^ p.L

/-! ## The shared block, from its base address `b0` on -/

/-- The directory: 32 cells, see `dirList`. -/
def aDIR (_p : Par) (b0 : ℕ) : ℕ := b0
/-- Powers of 3: `L + 1` cells. -/
def aP3 (_p : Par) (b0 : ℕ) : ℕ := b0 + 32
/-- Powers of 4: `L + 1` cells. -/
def aP4 (p : Par) (b0 : ℕ) : ℕ := p.aP3 b0 + (p.L + 1)
/-- Powers of 7: `L + 1` cells. -/
def aP7 (p : Par) (b0 : ℕ) : ℕ := p.aP4 b0 + (p.L + 1)
/-- Powers of 10: `L + 1` cells. -/
def aP10 (p : Par) (b0 : ℕ) : ℕ := p.aP7 b0 + (p.L + 1)
/-- Scratch for a row of Pascal's triangle: `L + 2` cells. -/
def aPAS (p : Par) (b0 : ℕ) : ℕ := p.aP10 b0 + (p.L + 1)
/-- The coefficients `φ_λ(s)`: 70 cells, row `λ` at `7 λ`. -/
def aPHI (p : Par) (b0 : ℕ) : ℕ := p.aPAS b0 + (p.L + 2)
/-- The coefficients `ψ_λ(t)`: 70 cells. -/
def aPSI (p : Par) (b0 : ℕ) : ℕ := p.aPHI b0 + 70
/-- The table of subsets: `K₀²` rows of `L` bits, the subset of the block product `(g, h)` in row
`g K₀ + h`. -/
def aMASK (p : Par) (b0 : ℕ) : ℕ := p.aPSI b0 + 70
/-- The band of every row: `N` cells. -/
def aBAND (p : Par) (b0 : ℕ) : ℕ := p.aMASK b0 + p.KK * p.L
/-- The block, within its band, of every row: `N` cells. -/
def aBLOCK (p : Par) (b0 : ℕ) : ℕ := p.aBAND b0 + p.N
/-- The base-3 digits of the offset of every row within its block: `N` rows of `L - m` cells, most
significant digit first. -/
def aDIG3 (p : Par) (b0 : ℕ) : ℕ := p.aBLOCK b0 + p.N
/-- The base-4 digits of every column of `X`: `D` rows of `m` cells, most significant digit first.
-/
def aDIG4 (p : Par) (b0 : ℕ) : ℕ := p.aDIG3 b0 + p.N * p.Lo
/-- The encodings of the row bands: band `β` at `β 10^L`. -/
def aENCA (p : Par) (b0 : ℕ) : ℕ := p.aDIG4 b0 + p.D * p.m
/-- The encodings of the column bands. -/
def aENCB (p : Par) (b0 : ℕ) : ℕ := p.aENCA b0 + p.nB * p.T
/-- The input array of the band that is being encoded: `7^L` cells.  Dead after the shared stage.
-/
def aARR (p : Par) (b0 : ℕ) : ℕ := p.aENCB b0 + p.nB * p.T
/-- Scratch of the recursive encoding: `7^L` cells (`7^{L-1} + … + 1` are used). Dead after the
shared stage. -/
def aZS (p : Par) (b0 : ℕ) : ℕ := p.aARR b0 + p.S7
/-- The first address after the shared block. -/
def sharedEnd (p : Par) (b0 : ℕ) : ℕ := p.aZS b0 + p.S7

end Par

/-- The content of the first 31 cells of the directory (the shared stage does not use the last one);
`aX` and `aY` are the addresses of `X` and `Y`. -/
def dirList (p : Par) (aX aY b0 : ℕ) : List ℕ :=
  [p.L, p.m, p.N, p.D, p.Lo, p.N0, p.K, p.K0, p.KK, p.nB, p.T, p.S7, aX, aY, p.aP3 b0, p.aP4 b0,
    p.aP7 b0, p.aP10 b0, p.aPAS b0, p.aPHI b0, p.aPSI b0, p.aMASK b0, p.aBAND b0, p.aBLOCK b0,
    p.aDIG3 b0, p.aDIG4 b0, p.aENCA b0, p.aENCB b0, p.aARR b0, p.aZS b0, p.sharedEnd b0]

/-! ## The private block of Theorem 5

The solver receives `N`, `D`, the number `w` of wanted positions, a bound `U` on the entries, the
addresses of `X`, `Y` (row by row), of the rows `WI` and the columns `WJ` of the wanted positions
and of the output, and as last argument the free pointer `fr`. All inputs and the output lie below
`fr`. The solver may write the output and the cells from `fr` on, and nothing is assumed about these
cells: a routine clears what it needs cleared. The shared block starts at `fr`, the private block
follows it. -/

namespace Par




























end Par

/-! ## The places and the sizes, as equations and inequalities -/














namespace Par
variable (p : Par)





























end Par











end Light.Sec2


