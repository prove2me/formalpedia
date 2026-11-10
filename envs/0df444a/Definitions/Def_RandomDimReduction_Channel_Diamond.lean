-- Prove2me | Definitions.Def_RandomDimReduction_Channel_Diamond
-- name    : RandomDimReduction_Channel_Diamond
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T11:23:52.340536+00:00
-- url     : https://prove2.me/theorems/d2f3a2d1-49df-4eaa-b59b-4ff6e2f860de
-- title:
--   Unhalved diamond norm for rectangular operator maps
-- statement:
--   For a map $f:L(A)\to L(B)$, stabilization leaves a reference copy of $A$ untouched and applies $f$ to each input block. Define
--   $$ \|f\|_\diamond=\sup_{\|Y\|_1\le1}\|(\operatorname{id}_A\otimes f)(Y)\|_1. $$
--   The trace norm is the published $\operatorname{Re}\operatorname{tr}\sqrt{Y^\dagger Y}$, with no factor $1/2$. The supremum is represented in extended nonnegative reals, avoiding any unbounded-real-supremum default. On the finite-dimensional complex-linear maps used here it is the usual finite diamond norm.
--
--   The interface supports different input and output dimensions and arbitrary entangled reference inputs.
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Theorems 1.1 and 5.1, pp.2,15; diamond-norm convention. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Tensor
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

set_option autoImplicit false

noncomputable section
open Matrix
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Stabilization of a map by an untouched reference, block by block. -/
def stabilize {a b r : Type} (f : Op a → Op b) (Y : Op (r × a)) : Op (r × b) :=
  fun i j => f (fun x y => Y (i.1, x) (j.1, y)) i.2 j.2

/-- Unhalved stabilized induced trace norm. The reference has the input dimension.
An extended nonnegative supremum avoids the default of a real unbounded supremum.
On the linear maps used by the theorems this is finite, and equals the usual norm. -/
def diamond {a b : Type} [Fintype a] [Fintype b]
    (f : Op a → Op b) : ℝ≥0∞ :=
  ⨆ Y : Op (a × a), ⨆ (_ : QAlgorithms.traceNorm Y ≤ 1),
    ENNReal.ofReal (QAlgorithms.traceNorm (stabilize f Y))

end RandomDimReduction.Channel


