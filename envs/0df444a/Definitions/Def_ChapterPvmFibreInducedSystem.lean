-- Prove2me | Definitions.Def_ChapterPvmFibreInducedSystem
-- name    : ChapterPvmFibreInducedSystem
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-16T20:39:37.117919+00:00
-- url     : https://prove2.me/theorems/d7742914-7e06-457b-b0b4-cdbb7c163478
-- title:
--   ChapterPvmFibreInducedSystem
-- statement:
--   ChapterPvmFibreInducedSystem

import Definitions.Def_ChapterPvmInducedSystem
import Definitions.Def_ChapterL2FibreSum
import Definitions.Def_ChapterHilbertSumIntertwine
import Definitions.Def_ChapterMackeyQuasiInvariant
import Definitions.Def_ChapterPvmCyclicDecomposition
import Definitions.Def_ChapterPvmCyclicUnitary
import Definitions.Def_ChapterPvmMeasure
import Mathlib


/-!
# The induced system on `L²(X, μ; K)` with a multiplicity (fibre) Hilbert space

`BookProof.ChapterPvmInducedSystem` writes an arbitrary projection-valued measure as the
`ℓ²`-sum of the multiplication systems of the cyclic pieces, indexed by a multiplicity set
`S`.  `BookProof.ChapterL2FibreSum` identifies, for a countable index `ι`, the `ℓ²`-sum of
copies of `L²(X, μ)` with the vector-valued space `L²(X, μ; ℓ²(ι))` of Mackey's *induced*
system.  Putting the two together gives the induced system in the form of
`BookProof.ChapterMackeyQuasiInvariant`: a **single** unitary onto `L²(X, μ; K)` with the
fibre (multiplicity) Hilbert space `K = ℓ²(ι)`, carrying `P(E)` to multiplication by `1_E`.

## Results

* `lpCongr` — the identification of the `L²` spaces of two equal measures, and
  `lpCongr_symm_proj`, its compatibility with multiplication by indicators.
* **`induced_system_of_isHilbertSum`** — if `H` is the Hilbert sum of countably many copies
  of `L²(X, μ)` along isometries carrying multiplication by `1_E` to `P(E)`, then there is a
  unitary `W : H ≃ L²(X, μ; ℓ²(ι))` with `W (P(E) v) = 1_E · W v`: the system *is* the
  induced one on the fibre `ℓ²(ι)`.
* **`pvm_induced_system_homogeneous`** — the concrete form: a projection-valued measure with
  a countable total orthogonal cyclic family whose fibre measures are all the *same* measure
  `μ` (homogeneous multiplicity) is unitarily the multiplication system on `L²(X, μ; ℓ²(S))`.

Everything is `sorry`-free and uses only the standard axioms.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace BookProof.ChapterPvmFibreInducedSystem

open BookProof.ChapterPvmMeasure BookProof.ChapterPvmCyclicUnitary
open BookProof.ChapterPvmCyclicDecomposition BookProof.ChapterPvmInducedSystem
open BookProof.ChapterMackeyQuasiInvariant BookProof.ChapterL2FibreSum
open BookProof.ChapterHilbertSumIntertwine

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The `L²` spaces of two equal measures -/

/-- Equal measures have the same `L²` space. -/
noncomputable def lpCongr {μ ν : Measure X} (h : μ = ν) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν := by
  subst h
  exact LinearIsometryEquiv.refl ℂ _



/-! ## The abstract form -/



/-! ## The homogeneous case of the cyclic decomposition -/

section Homogeneous

variable {P : Pvm X H} {S : Set H} {μ : Measure X}

/-- The model of the piece of `ψ`, read on the common measure `μ`. -/
noncomputable def homEmb (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) (ψ : S) :
    Lp ℂ 2 μ →ₗᵢ[ℂ] H :=
  (swIsom P (ψ : H)).comp (lpCongr (hmu ψ)).symm.toLinearIsometry









end Homogeneous

end BookProof.ChapterPvmFibreInducedSystem


