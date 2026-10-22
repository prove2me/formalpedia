-- Prove2me | Definitions.Def_TheoremB
-- name    : TheoremB
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-09T05:29:08.605825+00:00
-- url     : https://prove2.me/theorems/8937bdc5-376a-43ed-863d-51dceb1aebd9
-- title:
--   Theorem B: sharp portfolio value $\sup_f S_N(f) = \tau_N$ over the five algorithms
-- statement:
--   This module assembles Theorem B: over the five declared strategies of §21 — gradient descent with step $1/L$, gradient descent with step $1/(2L)$, rational-momentum NAG, fixed-seed random search, and grid-then-refine — the worst-case portfolio value equals the same sharp constant as NAG alone:
--
--   $$\sup_f S_N(f) = \tau_N = \frac{2}{N^2 + 7N + 4}, \qquad N \ge 1, \qquad S_N(f) = \min_{A} q_{A,N}(f), \qquad q_{A,N}(f) = \frac{f(x_{\mathrm{out},A}) - f^\star}{L R^2}.$$
--
--   The objects introduced are: the declared output tuple $A \mapsto x_{\mathrm{out},A}$ of the five strategies in normalised coordinates (`portfolioOutputOf`); the set of portfolio values of the normalised admissible instances, whose least upper bound is the theorem (`portfolioValueSet`, with the extremiser dimension $D = 2N+1$ of (23.1)); the scaled output tuple $x_{\mathrm{init}} + R \bullet z_A$ for general $L, R, x_{\mathrm{init}}$ (`portfolioOutputScaled`, source line 2749); and the single named hypothesis `TheoremAUpper`, which is exactly the general-form upper half $q_{\mathrm{NAG},N}(f) \le \tau_N$ standing in for the not-yet-assembled Theorem A. All quantifiers range over the outputs of the five fixed strategies and never over arbitrary algorithms (§36.4); the random-search list is fixed in advance (§36.3).
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §21-§22, §31-§32, §36, eq. (B), (23.1), (32.1); Lean: FullFormalization.TheoremB lines 1-244

-- Generated from F:/20261008/FullFormalization\FullFormalization\TheoremB.lean by skeleton subtraction (Phase 3-4):
-- every unselected declaration deleted, project imports rewritten.
/-
  FullFormalization.TheoremB

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, sections 21, 22,
  31, 32 and 36.  This file is the *assembly* of Theorem B,

      sup_f S_N(f) = tau_N = 2 / (N^2 + 7 N + 4),      N >= 1            (B)

  from pieces that are already verified elsewhere.  The portfolio value is
  `PortfolioDefinitions.SNOf`: the minimum of the five normalised losses
  `q_{A,N}(f) = (f(x_{out,A}) - f⋆) / (L R^2)` of the five constructors of
  `PortfolioDefinitions.Strategy` (source lines 2079-2096).

  The two halves of (B) come from two different files.

  * **Upper half, source §22 (lines 2107-2150).**  `S_N(f) ≤ q_{NAG,N}(f) ≤ tau_N`:
    the portfolio minimum is at most the rational-NAG loss because `SN` is a
    `min` over the five strategies (`SN_le` at `Strategy.nag`, wired through
    `SNOf_le`), and the rational-NAG loss is bounded by `tau_N` by **Theorem A**
    (source (A), sections 17-20).  Here: `portfolio_upper_bound` (general
    `L, R, x_init`), `portfolio_upper_bound_normalized` (the `L = R = 1`,
    `x_init = 0` form, quantified over every admissible `f`).

  * **Lower half, source §§23-31 (lines 2152-2690).**  `CommonExtremizer.lean`
    builds the lifted Huber extremiser on the hidden direction `u` of Lemma 24.1
    in dimension `D = 2N+1` (source (23.1)) and proves on it
    `q_NAG = tau_N`, `q_GD ≥ tau_N`, `q_halfGD ≥ tau_N`, `q_rand > tau_N`,
    `q_grid > tau_N`, hence `S_N(f_N) = tau_N`.  This file re-uses those results
    verbatim through `exists_extremizer` and `theoremB_lower_bound`:
    `exists_extremizer_normalized`, `theoremB_lower_bound_eps`,
    `theoremB_sup_normalized`, `theoremB_normalized`.

  * **General scales, source §32 (lines 2688-2751).**  The extremiser of
    §§23-31 is built for `L = R = 1`, `x_init = 0`.  The scaling (32.1)

        f(x) = L R^2 f_N((x - x_init)/R)

    transports it to arbitrary `L > 0`, `R > 0`, `x_init`, and — source line
    2749 — leaves every `q_{A,N}` unchanged.  Here: `portfolioOutputScaled`,
    `qLoss_scaled` (from `Scaling.normalizedLoss_scaled`), and
    `portfolio_extremizer_scaled`.  The assembled headline `theoremB` fixes
    neither `L = R = 1` nor `x_init = 0`.

  **The single external input.**  `TheoremA.lean` does not exist in this project
  yet: the all-`N` upper bound (17.1) is not assembled because the concrete
  interior/terminal certificate identities (10.1)/(11.1) are still in progress
  (`FORMALIZATION_STATUS.md`, "Remaining gaps" 1-3).  Theorem A therefore enters
  this file as the single *named hypothesis*

      TheoremAUpper N E : ∀ L R f x_init xstar, 0 < R → Admissible L R f x_init xstar →
                            qLoss L R f (f xstar) (nagX f L x_init N) ≤ tau N,

  i.e. exactly the source's `q_{NAG,N}(f) ≤ tau_N` of §22 in the general form of
  Theorem A's statement (A).  Every theorem below carries it explicitly; the
  dependency is recorded in the docstring of each theorem that uses it.  Nothing
  else is assumed, and the file contains no `sorry`, `admit`, `axiom` or `unsafe`.

  **A note on `CommonExtremizer.theoremB_sup_eq_tau`.**  That theorem takes the
  universal upper bound as the hypothesis
  `hUpper : ∀ (u : GridSpace N) (out : Strategy → GridSpace N), SNOf 1 1
  (liftedHuber u N) (liftedHuber u N u) out ≤ tau N`, i.e. for an *arbitrary*
  tuple `out` of outputs.  That hypothesis is not derivable from Theorem A and is
  in fact false: `S_N` is the minimum of the five losses, so for a unit vector `u`
  taking all five outputs equal to a far-away point `t • w` (`w ⊥ u`, `‖w‖ = 1`,
  `t → ∞`) gives, by `CommonExtremizer.liftedHuber_eq_BN_of_inner_zero` and
  `LiftedHuber.liftedHuber_self`,

      SNOf 1 1 (liftedHuber u N) (liftedHuber u N u) (fun _ => t • w)
        = liftedHuber u N (t • w) - 0 = B_N + t^2/2 > tau_N      (`BN_sub_tau_pos`).
  The faithful reading of §22 is the one used below: the bound is stated for the
  *declared* portfolio outputs (the five concrete strategy runs, source §21), of
  which only the rational-NAG entry is read off.  `portfolio_upper_bound` is
  correspondingly stated for every output tuple whose NAG component is the
  genuine rational-NAG output — a strengthening of the needed statement, and one
  that the declared tuple satisfies by definition.

  **Scope (source §36, lines 2898-2912).**  The three scope conditions of the
  source are visible in the statements below.

  * (36.2) the common extremiser's dimension may depend on `N`; the sufficient
    construction is `D = 2N+1`.  This is the type `GridSpace N =
    EuclideanSpace ℝ (Fin (gridDim N))` with `GridRefine.gridDim N = 2*N+1`;
    `finrank_gridSpace` records that its dimension is `2*N+1`.
  * (36.3) random search runs on a **fixed predetermined query list**
    `q : Fin N → GridSpace N` — the source's fixed public seed
    (`RandomSearch.sampleSeed`); `q` is a parameter given *before* the function,
    and nothing below uses any property of the concrete PRNG stream.
  * (36.4) the result concerns exactly the five constructors of
    `PortfolioDefinitions.Strategy`; `SN` is the `min` over those five, and no
    quantifier over arbitrary algorithms appears anywhere.  The quantifiers over
    `out : Strategy → E` below range over *outputs* of those five fixed
    strategies (each `out A` is determined by the run of strategy `A` on the
    function), not over algorithms.

  **Scalar-multiplication note.**  As everywhere in this project, every scalar
  multiple of a vector is written with an explicitly typed scalar
  (`((1 : ℝ) / 2) • v`, not `(1 / 2) • v`), because a bare numeral after `•` is
  elaborated at `ℕ`.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_CommonExtremizer
import Definitions.Def_FunctionClass
import Definitions.Def_GradientStrategies
import Definitions.Def_GridRefine
import Definitions.Def_HiddenDirection
import Definitions.Def_LiftedHuber
import Definitions.Def_PortfolioDefinitions
import Definitions.Def_RandomSearch
import Definitions.Def_RationalNAG
import Definitions.Def_Scaling

open scoped Gradient RealInnerProductSpace
open Set

set_option linter.unusedSectionVars false

namespace FullFormalization

noncomputable section

/-! ## 0.  The single external input: Theorem A's upper bound

`TheoremA.lean` is not present in this project (see the module docstring), so the
one thing this file cannot prove is isolated as a named proposition.  It is
exactly the source's `q_{NAG,N}(f) ≤ tau_N` (the first display of §22) in the
general form in which Theorem A (source (A), §17-§20) states its bound. -/

/-- **Theorem A (upper half), source (A), sections 17-20:** for every admissible
function in a finite-dimensional Euclidean space — `L > 0`, `f` differentiable
and convex, `∇f` globally `L`-Lipschitz, `xstar` a minimiser, `‖x_init - xstar‖ ≤ R`
— the rational-NAG output `nagX f L x_init N` satisfies

    (f(nagX f L x_init N) - f xstar) / (L R^2) ≤ tau_N = 2 / (N^2 + 7 N + 4).

This is the *only* statement this file assumes; it is the dependency on
`TheoremA.lean`, which is not yet assembled (`FORMALIZATION_STATUS.md`,
"Remaining gaps" 3).  Section 36.1 ("the NAG theorem covers any finite-dimensional
`L`-smooth convex function") is visible as the `[FiniteDimensional ℝ E]` instance. -/
def TheoremAUpper (N : ℕ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] : Prop :=
  ∀ (L R : ℝ) (f : E → ℝ) (x_init xstar : E), 0 < R → Admissible L R f x_init xstar →
    qLoss L R f (f xstar) (nagX f L x_init N) ≤ tau N

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]



/-! ## 1.  Section 22: the portfolio upper bound -/





/-! ### The declared five-strategy output map of §21

`CommonExtremizer.portfolioOutput` is the declared output tuple `A ↦ x_{out,A}` for
the extremiser family: `GD.out` with step `1`, `halfGD.out` with step `1`,
`nagX · 1 0 N`, the fixed-seed random search on the predetermined list `q`, and
grid-then-refine.  The map below is the same tuple for an *arbitrary* function of
`GridSpace N`; it agrees with `portfolioOutput` on the extremisers
(`portfolioOutputOf_liftedHuber`). -/

/-- The five declared strategies' outputs (source §21, lines 2079-2083, in the
source's order) on an arbitrary function of `GridSpace N`, in the normalised
coordinates `L = R = 1`, `x_init = 0`:

* `gd` — gradient descent, step `1/L = 1`;
* `halfGD` — gradient descent, step `1/(2L) = 1/2`;
* `nag` — rational-NAG (momentum `k/(k+3)`, step `1/L`);
* `rand` — fixed-seed random search on the predetermined list `q` (source's fixed
  public seed, §36.3);
* `grid` — grid-then-refine.

This is an enumeration over exactly the five `Strategy` constructors: there is no
quantifier over algorithms (§36.4). -/
noncomputable def portfolioOutputOf (N : ℕ) (f : GridSpace N → ℝ) (q : Fin N → GridSpace N)
    (hN : 0 < N) : Strategy → GridSpace N
  | Strategy.gd => GD.out (oracleOf f) 1 N
  | Strategy.halfGD => halfGD.out (oracleOf f) 1 N
  | Strategy.nag => nagX f 1 0 N
  | Strategy.rand => RandomSearch.out (oracleOf f) q hN
  | Strategy.grid => GridRefine.out N (oracleOf f)





/-! ## 2.  Section 31: the lower bound, in this file's output convention -/





/-- The set of portfolio values `S_N(f)` of the normalised admissible instances
(`L = R = 1`, `x_init = 0`), with the five strategies run as declared on the
predetermined query list `q`.  Its least upper bound is Theorem B. -/
def portfolioValueSet (N : ℕ) (q : Fin N → GridSpace N) (hN : 0 < N) : Set ℝ :=
  {v | ∃ (f : GridSpace N → ℝ) (u : GridSpace N), AdmissibleUnique 1 1 f 0 u ∧
        v = SNOf 1 1 f (f u) (portfolioOutputOf N f q hN)}





/-! ## 3.  Section 32: general `L, R, x_init` -/

/-- The declared five-strategy output tuple for the general instance obtained from
the extremiser `liftedHuber u N` by the scaling (32.1): the raw-space image
`x_init + R • z_A` of each normalised output `z_A`.

Source line 2749 ("算法均按公开 `R` 在 normalized coordinates 中运行，归一化轨迹与
`L = R = 1` 完全一致"): running the declared strategies in the normalised
coordinates of §21 and mapping the result back by (32.1) produces exactly these
points, and `qLoss_scaled` below shows the losses are those of the normalised
instance. -/
noncomputable def portfolioOutputScaled {N : ℕ} (R : ℝ) (x_init : GridSpace N)
    (u : GridSpace N) (q : Fin N → GridSpace N) (hN : 0 < N) : Strategy → GridSpace N :=
  fun A => x_init + R • portfolioOutput N u q hN A







/-! ## 4.  Sections 31 and 32 combined: Theorem B -/





end

end FullFormalization


