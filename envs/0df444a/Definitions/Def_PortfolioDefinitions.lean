-- Prove2me | Definitions.Def_PortfolioDefinitions
-- name    : PortfolioDefinitions
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-09T05:13:46.186057+00:00
-- url     : https://prove2.me/theorems/04e0c4af-67f0-45f3-9d2f-de229b924380
-- title:
--   Five-algorithm portfolio: oracle interface, normalized coordinates, per-strategy loss, portfolio minimum
-- statement:
--   This module fixes the objects of the five-algorithm problem of §21. The `Oracle E` structure is the query interface every strategy is written against: a single call at a point returns both a function value and a gradient, mirroring the frozen `oracle.query(point)`; `oracleOf f = ⟨f, ∇f⟩` is the canonical instance, for which the frozen smooth-convex algorithms are the Lean definitions verbatim. Normalized coordinates are the change of variables $z = (x - x_{\rm init})/R$ (source line 2074), with `toNormalized` and `ofNormalized` the two directions and $R \ne 0$ needed for the round trips. The per-strategy loss is
--
--   $$q_{A,N}(f) = \frac{f(x_{\mathrm{out},A}) - f_\star}{L R^2}$$
--
--   (source line 2090), and the portfolio value is
--
--   $$S_N(f) = \min_A q_{A,N}(f)$$
--
--   (source line 2096). `Strategy` is the required fixed five-element enumeration — `gd`, `halfGD`, `nag`, `rand`, `grid`, in the source's order — with no quantifier over algorithms anywhere; `SN` is the minimum over exactly these five, and `qLossVec` / `SNOf` package the vector of the five losses and the resulting portfolio value for a given strategy-output map.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §21 source lines 2057-2106 (also lines 2074, 2090, 2096); Lean: FullFormalization.PortfolioDefinitions lines 1-211

-- Generated from F:/20261008/FullFormalization\FullFormalization\PortfolioDefinitions.lean by skeleton subtraction (Phase 3-4):
-- every unselected declaration deleted, project imports rewritten.
/-
  FullFormalization.PortfolioDefinitions

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, sections 21 and
  30 (Theorem B, the five-algorithm portfolio).

  Section 21 fixes the objects this file defines:

    * the upstream task publishes `L > 0`, `R > 0` and `x_init`;
    * the function class is the differentiable convex globally `L`-smooth
      class of `FunctionClass.lean` (`Admissible`, with the unique-minimizer
      refinement `AdmissibleUnique`, source line 2065);
    * the five strategies run in the **normalized coordinate**

          z = (x - x_init) / R            (source line 2074),

      namely (1) GD with step `1/L`, (2) GD with step `1/(2L)`,
      (3) rational-NAG, (4) fixed-seed random search, (5) grid-then-refine;
    * the per-strategy loss is

          q_{A,N}(f) = (f(x_{out,A}) - f*) / (L R^2)     (source line 2090),

      and the portfolio value is

          S_N(f) = min_A q_{A,N}(f)                       (source line 2096).

  Representation choices:

  * `Oracle` is the query interface every strategy is written against: one
    oracle call returns a value *and* a gradient, exactly as the frozen
    implementation's `oracle.query(point)` returns `{"value": ..,
    "gradient": ..}` (`blackbox_algos.py`, `_gd_fixed_1_over_L` et al.).  The
    canonical instance for a differentiable function `f` is `oracleOf f`, whose
    gradient field is Mathlib's `∇ f` (`oracleOf_gradient`, defeq); the
    definitional equality is what makes `RationalNAG.nagX` — which is written
    against `∇ f` — literally the frozen Nesterov loop.

  * `toNormalized` / `ofNormalized` are the two directions of the change of
    variables (source line 2074).  `R ≠ 0` is needed for the round trips; the
    source has `R > 0` (line 2062).

  * `Strategy` is the five-element enumeration required by
    `DEPENDENCY_MAP.md` §36.4 ("`PortfolioDefinitions.Strategy` 为五元 `Fin 5`
    枚举，无 `∀` 量词"): five constructors, in the source's order 1-5.  There is
    no quantifier over algorithms anywhere in the portfolio; `SN` is the
    minimum over exactly these five.

  * `SN` takes the vector of the five per-strategy losses `Strategy → ℝ`.  The
    losses themselves are produced by the concrete runs of
    `GradientStrategies.lean`, `RandomSearch.lean` and `GridRefine.lean` (and
    `RationalNAG.lean` for strategy 3); `SNOf` packages that wiring, so
    `SNOf L R f fstar out` *is* the source's `S_N(f)` for the five outputs
    `out : Strategy → E`.
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*}

/-! ### The oracle -/

/-- One query interface: a call at a point `x` returns the function value
`value x` and the gradient `gradient x`.  Every strategy of section 21 spends
exactly one call per step and never queries a point it does not use (the
`blackbox_algos.py` header states this as the invariant of the frozen set). -/
structure Oracle (E : Type*) where
  /-- the value the oracle reports at a query point -/
  value : E → ℝ
  /-- the gradient the oracle reports at a query point -/
  gradient : E → E

namespace Oracle







end Oracle

section OracleOf

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The canonical oracle of a differentiable function: value `f`, gradient
`∇ f`.  For this oracle the frozen smooth-convex algorithms of
`blackbox_algos.py` are the Lean definitions verbatim. -/
noncomputable def oracleOf (f : E → ℝ) : Oracle E := ⟨f, ∇ f⟩





end OracleOf

/-! ### What a strategy run produces -/



/-! ### Normalized coordinates (source line 2074) -/

section Normalized

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]













end Normalized

/-! ### The loss of one strategy (source line 2090) -/

section Loss

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Source line 2090: `q_{A,N}(f) = (f(x_{out,A}) - f*)/(L R^2)`.  The output
point is a parameter; which point a strategy outputs is the content of the
respective strategy file. -/
noncomputable def qLoss (L R : ℝ) (f : E → ℝ) (fstar : ℝ) (out : E) : ℝ :=
  (f out - fstar) / (L * R ^ 2)





end Loss

/-! ### The five strategies and the portfolio minimum (source lines 2079-2096) -/

/-- Source lines 2079-2083: the five strategies, in the source's order.

    1. `gd`     — gradient descent, step `1/L`;
    2. `halfGD` — gradient descent, step `1/(2L)`;
    3. `nag`    — rational-NAG (momentum `k/(k+3)`, step `1/L`);
    4. `rand`   — fixed-seed random search;
    5. `grid`   — grid-then-refine.

This is the five-element enumeration of `DEPENDENCY_MAP.md` §36.4: a fixed
finite list, with no quantifier over algorithms. -/
inductive Strategy where
  | gd
  | halfGD
  | nag
  | rand
  | grid
  deriving DecidableEq

instance : Fintype Strategy :=
  Fintype.ofList [Strategy.gd, Strategy.halfGD, Strategy.nag, Strategy.rand, Strategy.grid]
    (by intro x; cases x <;> simp)

instance : Nonempty Strategy := ⟨Strategy.gd⟩

/-- Source line 2096: `S_N(f) = min_A q_{A,N}(f)`, the minimum over the five
strategies of section 21.  The argument is the vector of the five losses. -/
noncomputable def SN (q : Strategy → ℝ) : ℝ :=
  min (min (min (min (q Strategy.gd) (q Strategy.halfGD)) (q Strategy.nag))
    (q Strategy.rand)) (q Strategy.grid)







section Portfolio

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The five per-strategy losses of section 21, as a vector indexed by the five
strategies: `A ↦ q_{A,N}(f)`. -/
noncomputable def qLossVec (L R : ℝ) (f : E → ℝ) (fstar : ℝ) (out : Strategy → E) :
    Strategy → ℝ :=
  fun A => qLoss L R f fstar (out A)

/-- The source's `S_N(f) = min_A q_{A,N}(f)`, given the five strategies' output
map `out`.  A later module instantiates `out` with the concrete runs of
`GradientStrategies.lean`, `RandomSearch.lean` and `GridRefine.lean` (and the
rational-NAG run for `Strategy.nag`). -/
noncomputable def SNOf (L R : ℝ) (f : E → ℝ) (fstar : ℝ) (out : Strategy → E) : ℝ :=
  SN (qLossVec L R f fstar out)





end Portfolio

end FullFormalization


