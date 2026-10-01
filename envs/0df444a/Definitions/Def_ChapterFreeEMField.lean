-- Prove2me | Definitions.Def_ChapterFreeEMField
-- name    : ChapterFreeEMField
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:58:12.517458+00:00
-- url     : https://prove2.me/theorems/981b103e-9e9b-44d0-9558-ce0b96b70af3
-- title:
--   Chapter FreeEMField
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFreeEMField.lean`): generated def bundle for ChapterFreeEMField. See BookProof/ChapterFreeEMField.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFreeEMField.lean

import Definitions.Def_ChapterYangMillsFieldStrength
import Mathlib


/-!
# Chapter "Timepiece and the Gribov ambiguity", §"Free electromagnetic field: an exact example" —
the abelian reduction of the field strength

Source: `book.tex`, chapter *"Timepiece and the Gribov ambiguity"*,
§*"Free electromagnetic field: an exact example"* (line ~7413):

> *"While the free electromagnetic field is an abelian gauge theory and thus it
> is somewhat simpler than a Yang-Mills theory (for instance, there is no Gribov
> ambiguity), it has the crucial advantage that the time-evolution has an exact
> solution, because the Hamiltonian is quadratic in the fields. … The
> extrapolation of the results of the previous section to the electromagnetism is
> straightforward … we set the structure constants `f_{abc}` to zero. …
> Through time-evolution (in the Weyl gauge), we also have the local self-adjoint
> operator `∂×π`, i.e. the curl of the Electric Field."*

This continues `ChapterYangMillsFieldStrength.lean` (the non-abelian field
strength `F_{jk} = δ_j a_k - δ_k a_j + [a_j, a_k]`) by specializing to the
**abelian (electromagnetic) case**, where the connection components commute
(equivalently the structure constants `f_{abc}` vanish).  In that case:

* the quadratic `[a_j, a_k]` correction drops out, so the field strength reduces
  to the ordinary **exterior derivative / curl** `F_{jk} = ∂_j A_k - ∂_k A_j`,
  which is *linear* in the fields — this is exactly why "the Hamiltonian is
  quadratic in the fields" and admits an exact solution;
* this abelian field strength is **gauge invariant** under the abelian gauge
  transformation `A_j ↦ A_j + ∂_j θ` (the curl of a gradient vanishes),
  which is the abelian statement of "there is no Gribov ambiguity";
* the field strength / curl of *self-adjoint* operator fields (e.g. the curl of
  the electric field `∂×π`) is again **self-adjoint**, i.e. a genuine local
  observable.

## Main statements

* `emFieldStrength` — the abelian field strength `F_{jk} = δ_j (A_k) - δ_k (A_j)`
  (the exterior derivative / a single curl component);
* `emFieldStrength_antisymm` — `F_{jk} = - F_{kj}`;
* `emFieldStrength_gauge_invariant` — invariance under `A_j ↦ A_j + δ_j θ`
  (curl of a gradient vanishes; the abelian "no Gribov ambiguity");
* `fieldStrengthMul_eq_emFieldStrength_of_commute` — when the connection
  components commute, the non-abelian field strength of
  `ChapterYangMillsFieldStrength` equals the abelian one (the `f = 0` reduction);
* `Fbook_eq_emFieldStrength_of_commute` — the same reduction for the book's
  coupled field strength `Fbook`;
* `emFieldStrength_isSelfAdjoint` — the curl of self-adjoint operator fields is
  self-adjoint (the book's local self-adjoint `∂×π`).
-/

namespace BookProof.FreeEMField

open BookProof.YangMillsFieldStrength

section Abstract

variable {R : Type*} [Ring R]

/-- The **abelian field strength** (a single curl component / exterior
derivative) `F_{jk} = δ_j (A_k) - δ_k (A_j)`, where `δ_j` is the partial
derivative `∂_j` and `A_j` is the gauge potential.  This is the `f_{abc} = 0`
specialization of the non-abelian `fieldStrengthMul`. -/
def emFieldStrength (δ : Fin 3 → R → R) (A : Fin 3 → R) (j k : Fin 3) : R :=
  δ j (A k) - δ k (A j)







end Abstract

section Coupling

variable {R : Type*} [Ring R] [Algebra ℂ R]



end Coupling

section SelfAdjoint

variable {R : Type*} [Ring R] [StarRing R]



end SelfAdjoint

end BookProof.FreeEMField


