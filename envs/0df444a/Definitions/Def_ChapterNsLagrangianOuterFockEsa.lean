-- Prove2me | Definitions.Def_ChapterNsLagrangianOuterFockEsa
-- name    : ChapterNsLagrangianOuterFockEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-08T21:05:46.614878+00:00
-- url     : https://prove2.me/theorems/9a874b16-be25-4be9-a212-a241d5d5aec6
-- title:
--   ChapterNsLagrangianOuterFockEsa
-- statement:
--   ChapterNsLagrangianOuterFockEsa

import Definitions.Def_ChapterNavierStokesLagrangianCanonical
import Definitions.Def_ChapterNsLagrangianDetFarisLavine
import Definitions.Def_ChapterFockStatisticsEsa
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterYangMillsNonAbelianEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterYangMillsHermite
import Mathlib


/-!
# The Lagrangian Navier–Stokes one-particle Hamiltonian on the outer Fock space

The project already proves essential self-adjointness (ESA) of the Lagrangian
(parcel/trajectory) one-particle Hamiltonian:

* `LagrangianCanonical.lagCan_esa` — **unconditional.**  One parcel, trajectory space
  `ℓ²(Fin 3 → ℕ)` (the Hermite/occupation realization of `L²(ℝ³)`), operator
  `h = ½ Σᵢ Pᵢ² + ν Σᵢ Qᵢ² + Σᵢ fᵢ Pᵢ` on the finite-mode (Hermite) core, for every `ν > 0`
  and every constant force `f ∈ ℝ³`.  Proof: the second-order part is `ω(N + 3/2)`,
  `ω = √(2ν)`, diagonal in the Hermite basis, hence ESA; the drift `f·P` is Kato–Rellich
  bounded with relative bound `< 1`.

* `NsLagrangianDetFL.lagKoopman_esa_of_comparison_esa` — **conditional.**  Galerkin Lagrangian
  NS with the exact determinant constraint (penalty `V_κ`); ESA of the Koopman generator
  `H_L` follows *if* the comparison operator `N_L = H_L² + E` is ESA.

This module carries both statements to the outer Fock space with the general second
quantization theorems of the project:

* `EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa` — if `A` is symmetric and ESA on a
  dense `D`, then `dΓ(A)` is ESA on the finite-particle domain `𝓕_fin(D)`
  (algebraic direct sum over `n` of the algebraic tensor powers `D^{⊗n}`);
* `FockStatistics.bosonicFock_esa` / `fermionicFock_esa` and the Hilbert-space versions
  `hbosonicFock_esa` / `hfermionicFock_esa` — the same on the symmetric / antisymmetric Fock
  spaces.

No new hypothesis enters: for `lagCan` the results are unconditional, and for the Koopman
generator they inherit exactly the hypothesis on `N_L`.

## Scope

`dΓ(h)` is the *non-interacting* (number-conserving, one-body) outer Hamiltonian
`Σ_{ij} h_{ij} a†_i a_j`: on the `n`-parcel sector it acts as
`Σ_p 1 ⊗ ⋯ ⊗ h ⊗ ⋯ ⊗ 1`.  The parcel–parcel couplings of the gauge-fixed models
(`ChapterNavierStokesFullLagrangianFock`) are not of this form and are not covered.

Nothing is assumed: no `axiom`, no `sorry`.
-/

namespace BookProof.NsLagrangianOuterFock

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.FockStatistics BookProof.PermSector BookProof.ReducedEsa
open BookProof.DirectSumEsa BookProof.SecondQuantizationCore
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsNonAbelianEsa
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LagrangianCanonical
open BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.IkebeKato

noncomputable section

/-! ## 1. The unconditional case: the canonical Lagrangian parcel Hamiltonian -/

/-- The one-parcel trajectory space `ℓ²(Fin 3 → ℕ)`, bundled as a Hilbert space. -/
def lagOneSpace : IPSpace := ⟨L2I Vel⟩

instance : CompleteSpace lagOneSpace.carrier :=
  inferInstanceAs (CompleteSpace (L2I Vel))

/-- **The Lagrangian one-particle (one-parcel) Hamiltonian**
`h = ½ Σᵢ Pᵢ² + ν Σᵢ Qᵢ² + Σᵢ fᵢ Pᵢ` on the finite-mode (Hermite) core of `ℓ²(Fin 3 → ℕ)`. -/
def lagOneOp (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    lpFiniteModes Vel →ₗ[ℂ] lagOneSpace.carrier :=
  lagrangianCore (lagCanData nu hnu f)

















/-! ## 2. The conditional case: the Lagrangian Koopman generator with the determinant -/

section Koopman

open BookProof.NsLagrangianDetFL

variable {K : Type*} [Fintype K] (S : LagNsData K)





end Koopman

end

end BookProof.NsLagrangianOuterFock


