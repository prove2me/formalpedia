-- Prove2me | Definitions.Def_ChapterBddBelowFiberSumEsa
-- name    : ChapterBddBelowFiberSumEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-17T19:44:48.300841+00:00
-- url     : https://prove2.me/theorems/e7ed541c-c232-4bd2-9d87-b7ea976d5101
-- title:
--   A direct sum of bounded-below one-dimensional wall Hamiltonians
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.BddBelowFiberSumEsa`, source chapter `BookProof/ChapterBddBelowWallEsa.lean`): composition of bounded-below one-dimensional wall Hamiltonians. The one-particle space `fiberSpace = l^2(i, L^2(R))`, the glued core `fiberCore` (algebraic direct sum of the compactly supported smooth fibre cores), the composed operator `fiberSumHam = sum_i (-d^2/dx_i^2 + V_i)`, and the physical fibre list `qgFiberV`: `d` shear directions carrying harmonic walls `omega_i^2 x_i^2` together with one scalaron direction carrying the Starobinsky wall `starobinskyV M alpha`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBddBelowWallEsa.lean

import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterFarisLavineCore
import Mathlib


/-!
# QG-2 Case A, composed: a direct sum of bounded-below one-dimensional wall Hamiltonians

`BookProof/ChapterBddBelowWallEsa.lean` proves the one-dimensional input of
`CONSOLIDATED_PLAN.md`'s QG-2 **Case A**: `−d²/dx² + V` is essentially self-adjoint on the
compactly supported smooth core of `L²(ℝ)` for *every* smooth real potential bounded below,
with no growth and no sign hypothesis.  This module performs the **composition** step: it
glues an arbitrary family of such fibres into one operator on the orthogonal direct sum

`ℓ²(i : ι, L²(ℝ))`,   `H = ⊕ᵢ (−d²/dxᵢ² + Vᵢ)`,

and transports the three properties the plan asks of the composed object — essential
self-adjointness, the unitary flow it generates, and the lower bound on its quadratic form.

The gluing instrument is `BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn` (a deficiency
space of an orthogonal direct sum is the direct sum of the fibre deficiency spaces), so no
relative bound, no comparison operator and no commutator estimate is needed; the whole
analytic content sits in the one-dimensional fibre theorem.

## What is proved

* `fiberCore`, `fiberSumHam` — the glued core `⊕ᵃˡᵍ Cc^∞(ℝ)` and the glued operator
  `⊕ᵢ (−d²/dxᵢ² + Vᵢ)`, with `fiberSumHam_single` and `fiberSumHam_symmetricOn`;
* `fiberCore_dense` — the glued core is dense;
* **`fiberSumHam_essentiallySelfAdjoint_of_bddBelow`** — the composed operator is
  essentially self-adjoint as soon as *each* fibre potential is bounded below (each with its
  own constant); `fiberSumHam_essentiallySelfAdjoint_of_bddBelow'` is the `BddBelow` form and
  `fiberSumHam_essentiallySelfAdjoint_of_nonneg` the non-negative case;
* `fiberSumHam_stone_flow` — the composed operator therefore has a unique self-adjoint
  extension and generates the unitary group `e^{−itH}`;
* **`fiberSumHam_semibounded`** — with a *uniform* lower bound `Vᵢ ≥ −c` the quadratic form
  of the composed operator is bounded below by `−c` (the fibrewise Green identity of
  `BookProof.WallEsaSemibounded`, summed over the fibres), and `fiberSumHam_nonneg_form`
  for `Vᵢ ≥ 0`;
* `qgFiberSum_esa`, `qgFiberSum_nonneg_form` — the physical instance of QG-3.3's derived
  fibre list: `d` shear directions carrying harmonic walls `ωᵢ² xᵢ²` together with one
  scalaron direction carrying the Starobinsky wall `starobinskyV M α`.

## Honest boundary

The decomposition is an **orthogonal direct sum** of one-dimensional fibres, not a tensor
product: the space is `ℓ²(ι, L²(ℝ))`, and this module says nothing about `−Δ + V` on
`L²(ℝ^d)` (whose deficiency analysis would need multi-dimensional elliptic regularity, which
is not available here).  Uniform boundedness below is needed only for the *form* bound; for
essential self-adjointness the constants may vary from fibre to fibre.  Nothing here concerns
the wrong-sign conformal direction, which is Case B and where the conclusion is false
(`BookProof/ChapterConformalFiberDeficiency.lean`).
-/

namespace BookProof.BddBelowFiberSumEsa

open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallEsaSemibounded BookProof.DirectSumEsa

noncomputable section

variable {ι : Type*}

/-- The one-particle space of the composed model: the orthogonal direct sum of one copy of
`L²(ℝ)` per fibre. -/
abbrev fiberSpace (ι : Type*) := lp (fun _ : ι => Lp ℂ 2 (volume : Measure ℝ)) 2

/-- The glued core: the algebraic direct sum of the fibre cores of compactly supported
smooth functions. -/
def fiberCore (ι : Type*) : Submodule ℂ (fiberSpace ι) := dsCore (fun _ : ι => ccDomain ℝ)

/-- **The composed operator** `⊕ᵢ (−d²/dxᵢ² + Vᵢ)` on the glued core. -/
def fiberSumHam (V : ι → ℝ → ℝ) (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i)) :
    fiberCore ι →ₗ[ℂ] fiberSpace ι :=
  dsOp (fun i => wallHam (V i) (hV i))







/-! ## Essential self-adjointness of the composed operator -/









/-! ## The quadratic form of the composed operator -/







/-! ## The physical instance: shear walls plus the scalaron wall -/

/-- The fibre list of QG-3.3's derived reduction: `d` shear directions carrying the harmonic
walls `ωᵢ² xᵢ²`, and one scalaron direction carrying the Starobinsky wall. -/
def qgFiberV (M alpha : ℝ) {d : ℕ} (omega : Fin d → ℝ) : Option (Fin d) → ℝ → ℝ
  | none => fun phi => BookProof.Starobinsky.starobinskyV M alpha phi
  | some i => fun x => omega i ^ 2 * x ^ 2









end

end BookProof.BddBelowFiberSumEsa


