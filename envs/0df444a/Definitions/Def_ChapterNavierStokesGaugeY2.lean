-- Prove2me | Definitions.Def_ChapterNavierStokesGaugeY2
-- name    : ChapterNavierStokesGaugeY2
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:19:21.266844+00:00
-- url     : https://prove2.me/theorems/248a73f3-2773-4992-832a-9df0a327de4b
-- title:
--   Chapter NavierStokesGaugeY2
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesGaugeY2.lean`): generated def bundle for ChapterNavierStokesGaugeY2. See BookProof/ChapterNavierStokesGaugeY2.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesGaugeY2.lean

import Definitions.Def_ChapterNavierStokesGaugeY
import Mathlib


/-!
# The second-order second coordinate: `genY2` and the Laplacian modes

Source: `book.tex`, chapter *"Free field parametrization in Classical Statistical
Field Theory and Navier–Stokes equations"* (~4133–4216), and plan item **A.7** of
`PLAN_LEAN_SPECIALIST_NS_FLOW.md` (recorded in `CONSOLIDATED_PLAN.md` §9).

`BookProof.ChapterNavierStokesGaugeY` builds the second coordinate `y` and its
gauge generator `G_j = ∂/∂y_j − u_{i,j} ∂/∂u_i`; that generator compensates only
the *first*-derivative modes, i.e. it annihilates the **linear** field
`u_i(y) = u_i + u_{i,j} y_j`.  The Laplacian modes `u_{i,jj}` therefore sit in the
Hamiltonian without being tied to the expansion of the field.

This module carries out the second-order refinement.  With the same canonical
variables (`BookProof.NavierStokesGaugeY.NSVar`, whose `uL` constructor is the
Laplacian mode) it introduces

* the **second-order field**
  `u_i(y) = u_i + u_{i,j} y_j + ½ u_{i,jj} y_j²`  (`uField2`),
  the genuine Taylor expansion to second order (the `½` is the Taylor
  coefficient; perturbing it breaks the invariance, see
  `genY2_uField2_perturbed_ne_zero`);
* the **derivative field** `u_{i,j}(y) = u_{i,j} + u_{i,jj} y_j` (`uDField`),
  which is exactly `∂ u_i(y)/∂ y_j` (`uField2_pderiv_y`);
* the **second-order gauge generator**
  `G²_j = ∂/∂y_j − u_{i,j} ∂/∂u_i − u_{i,jj} ∂/∂u_{i,j}`  (`genY2`).

The headline results are

* `genY2_uField2` — `G²_j` annihilates the second-order field, so the Laplacian
  modes are now legitimate gauge partners rather than spectators;
* `genY2_uDField` — it annihilates the derivative field as well;
* `genY2_nsSymbol2` — hence the Navier–Stokes symbol built from the *fields*,
  `A_i(y) = ∑_j u_j(y) u_{i,j}(y) − ν u_{i,jj}`, is gauge invariant, while
  `setYZero_nsSymbol2` shows that on the initial state `y = 0` it is the ordinary
  Navier–Stokes symbol `u_j u_{i,j} − ν u_{i,jj}`;
* sharpness in both directions: the first-order generator does **not** annihilate
  the second-order field (`genY_uField2`, `genY_uField2_ne_zero`) and the
  second-order generator does **not** annihilate the first-order field
  (`genY2_uField`, `genY2_uField_ne_zero`);
* `genY2_leibniz` — `G²_j` is a derivation, hence generates a one-parameter group
  of algebra automorphisms, and the second-order gauge algebra is abelian, i.e.
  first class (`genY2_genY2_commute`, `genX_genY2_commute`).

The mixed bracket is *not* zero and we say so honestly
(`genY_genY2_bracket_X_u`, `genY_genY2_not_commute`): the first- and the
second-order generators are truncations of the *same* gauge transformation at
different orders, and only the second-order one is a symmetry of the
second-order field.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NavierStokesGaugeY2

open MvPolynomial BookProof.NavierStokesGaugeY

/-! ## Two generic facts about derivations of the polynomial algebra -/







/-! ## The second-order field and the derivative field -/

/-- **The second-order field**: the Taylor expansion of the velocity in the
second coordinate carried one order further,
`u_i(y) = u_i + u_{i,j} y_j + ½ u_{i,jj} y_j²`. -/
noncomputable def uField2 (i : Fin 3) : NSAlg :=
  X (NSVar.u i) + (∑ j : Fin 3, X (NSVar.uD i j) * X (NSVar.y j))
    + C (1 / 2 : ℂ) * ∑ j : Fin 3, X (NSVar.uL i) * (X (NSVar.y j) * X (NSVar.y j))

/-- **The derivative field** `u_{i,j}(y) = u_{i,j} + u_{i,jj} y_j`: the first
derivative of the velocity, itself expanded to first order in `y`. -/
noncomputable def uDField (i j : Fin 3) : NSAlg :=
  X (NSVar.uD i j) + X (NSVar.uL i) * X (NSVar.y j)

/-! ### The partial derivatives of the second-order field -/











/-! ### The partial derivatives of the first-order field -/





/-! ## The second-order gauge generator -/

/-- **The second-order gauge generator**
`G²_j = ∂/∂y_j − u_{i,j} ∂/∂u_i − u_{i,jj} ∂/∂u_{i,j}`: translating the second
coordinate now shifts the velocity modes by their first derivatives *and* the
first-derivative modes by the Laplacian modes. -/
noncomputable def genY2 (j : Fin 3) : Module.End ℂ NSAlg :=
  (pderiv (NSVar.y j)).toLinearMap
    - (∑ i : Fin 3, (LinearMap.mulLeft ℂ (X (NSVar.uD i j) : NSAlg)) ∘ₗ
        (pderiv (NSVar.u i)).toLinearMap)
    - ∑ i : Fin 3, (LinearMap.mulLeft ℂ (X (NSVar.uL i) : NSAlg)) ∘ₗ
        (pderiv (NSVar.uD i j)).toLinearMap











/-! ### The action on the canonical variables -/











/-! ## Gauge invariance of the second-order field -/







/-! ### Sharpness: the two generators are genuinely different -/













/-! ### The second-order gauge algebra is abelian (first class) -/









/-! ## The Navier–Stokes symbol in second-order form -/

/-- The Navier–Stokes symbol built from the **fields**,
`A_i(y) = ∑_j u_j(y) u_{i,j}(y) − ν u_{i,jj}`. -/
noncomputable def nsSymbol2 (nu : ℂ) (i : Fin 3) : NSAlg :=
  (∑ j : Fin 3, uField2 j * uDField i j) - C nu * X (NSVar.uL i)





/-! ## The initial state `y = 0` -/







end BookProof.NavierStokesGaugeY2


