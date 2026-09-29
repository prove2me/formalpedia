-- Prove2me | Definitions.Def_ChapterHermiteGalerkinFriedrichs
-- name    : ChapterHermiteGalerkinFriedrichs
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:50:20.401968+00:00
-- url     : https://prove2.me/theorems/f526de77-139a-42a1-9d05-5c678e788242
-- title:
--   This module formalizes the argument that a Krylov/Galerkin algorithm run in a complete basis (the Hermite/oscillator bas ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.HermiteGalerkinFriedrichs`, source chapter `BookProof/ChapterHermiteGalerkinFriedrichs.lean`).
--
--   This module formalizes the argument that a Krylov/Galerkin algorithm run in a complete basis (the Hermite/oscillator basis) does not have to be told which self-adjoint extension of a semi-bounded symmetric Hamiltonian to use: the truncation is a Rayleigh–Ritz minimization of the *energy form*, and the sequence of finite-dimensional energy minimizations converges to the extension determined by the energy form — the Friedrichs extension.
--
--   The informal argument has three steps; here is what each becomes.
--
--   **Step 1 (the Rayleigh–Ritz connection).** Truncating to the span of the first `m` basis vectors replaces `H` by the compression `Pₘ H Pₘ`, and on that subspace the compression carries *exactly* the energy form of `H` (`inner_galerkinCompression`, `quadForm_galerkinCompression`). The associated Ritz values are the infima of the energy over unit vectors of the subspace; they are antitone in `m` (`ritzInf_antitone`) and converge to the infimum of the energy form over the whole domain (`ritzInf_tendsto_domainInf`). Moreover that limit dominates the ground-state energy of *every* positive self-adjoint extension (`ritzInf_extension_le`), the extension attaining it being the one whose energy form is the closure of the form of `H` — the Friedrichs extension. **No boundedness is used here.**
--
--   **Step 2 (the flag exhausts the form domain).** For the Hermite basis the domain is the span of the basis vectors, and *every* domain vector already lies in a finite Galerkin subspace (`exists_mem_galerkinSpan`), while the subspaces increase to a dense subspace (`galerkinSpan_iSup_dense`), so the projections converge strongly to the identity (`galerkinProj_tendsto`). This is the formal content of "`Pₘ → I` because the Hermite functions are complete", and of "the finite matrices explore larger and larger subspaces of the energy form".
--
--   **Step 3 (the limit is the Friedrichs extension).** In the regime where the operator is bounded on its domain — the regime in which the limit of the truncations exists as an operator, and the only regime claimed here — we prove:
--
--   * the compressions converge strongly to the extension (`galerkinCompression_tendsto`, `compression_tendsto_of_starProjection_tendsto`); * the *resolvents* of the truncations converge strongly to the resolvent of the extension, for every non-real spectral parameter (`resolvent_tendsto_of_strong_tendsto`, `galerkinResolvent_tendsto`) — this is the Galerkin/Rayleigh–Ritz strong-resolvent-convergence statement quoted in the informal argument; * the extension so obtained is the **unique** positive self-adjoint extension (`positive_selfadjoint_extension_unique`), i.e. the algorithm has no freedom left: what it converges to is the Friedrichs extension.
--
--   The headline combination is `hermiteGalerkin_selects_friedrichs`.
--
--   * Everything in Step 3 carries an explicit boundedness hypothesis on the operator, exactly as in `BookProof.ChapterYangMillsFriedrichsLimit`. For a genuinely unbounded, non-essentially-self-adjoint operator the identification of the Galerkin limit with the Friedrichs extension is **not** proved here; only Steps 1 and 2 (the variational content) are unconditional. * Nothing about the indeterminate Stieltjes moment problem, Padé approximants or Nevanlinna-extremal measures is formalized. * The Hermite basis enters through the property that actually matters — it is a Hilbert basis indexed by `ℕ`, so its finite spans increase to a dense subspace. No property of Hermite polynomials beyond completeness and orthonormality is used, and the results apply verbatim to any complete orthonormal basis.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterFarisLavineCore

import Mathlib

/-!
# The Hermite-basis Galerkin (Rayleigh–Ritz) truncation and the Friedrichs extension

This module formalizes the argument that a Krylov/Galerkin algorithm run in a
complete basis (the Hermite/oscillator basis) does not have to be told which
self-adjoint extension of a semi-bounded symmetric Hamiltonian to use: the
truncation is a Rayleigh–Ritz minimization of the *energy form*, and the
sequence of finite-dimensional energy minimizations converges to the extension
determined by the energy form — the Friedrichs extension.

The informal argument has three steps; here is what each becomes.

**Step 1 (the Rayleigh–Ritz connection).**  Truncating to the span of the first
`m` basis vectors replaces `H` by the compression `Pₘ H Pₘ`, and on that
subspace the compression carries *exactly* the energy form of `H`
(`inner_galerkinCompression`, `quadForm_galerkinCompression`).  The
associated Ritz values are the infima of the energy over unit vectors of the
subspace; they are antitone in `m` (`ritzInf_antitone`) and converge to the
infimum of the energy form over the whole domain
(`ritzInf_tendsto_domainInf`).  Moreover that limit dominates the ground-state
energy of *every* positive self-adjoint extension (`ritzInf_extension_le`), the
extension attaining it being the one whose energy form is the closure of the
form of `H` — the Friedrichs extension.  **No boundedness is used here.**

**Step 2 (the flag exhausts the form domain).**  For the Hermite basis the
domain is the span of the basis vectors, and *every* domain vector already lies
in a finite Galerkin subspace (`exists_mem_galerkinSpan`), while the subspaces
increase to a dense subspace (`galerkinSpan_iSup_dense`), so the projections
converge strongly to the identity (`galerkinProj_tendsto`).  This is the
formal content of "`Pₘ → I` because the Hermite functions are complete", and of
"the finite matrices explore larger and larger subspaces of the energy form".

**Step 3 (the limit is the Friedrichs extension).**  In the regime where the
operator is bounded on its domain — the regime in which the limit of the
truncations exists as an operator, and the only regime claimed here — we prove:

* the compressions converge strongly to the extension
  (`galerkinCompression_tendsto`, `compression_tendsto_of_starProjection_tendsto`);
* the *resolvents* of the truncations converge strongly to the resolvent of the
  extension, for every non-real spectral parameter
  (`resolvent_tendsto_of_strong_tendsto`, `galerkinResolvent_tendsto`) — this is
  the Galerkin/Rayleigh–Ritz strong-resolvent-convergence statement quoted in
  the informal argument;
* the extension so obtained is the **unique** positive self-adjoint extension
  (`positive_selfadjoint_extension_unique`), i.e. the algorithm has no freedom
  left: what it converges to is the Friedrichs extension.

The headline combination is `hermiteGalerkin_selects_friedrichs`.

## Scope — what is *not* claimed

* Everything in Step 3 carries an explicit boundedness hypothesis on the
  operator, exactly as in `BookProof.ChapterYangMillsFriedrichsLimit`.  For a
  genuinely unbounded, non-essentially-self-adjoint operator the identification
  of the Galerkin limit with the Friedrichs extension is **not** proved here;
  only Steps 1 and 2 (the variational content) are unconditional.
* Nothing about the indeterminate Stieltjes moment problem, Padé approximants or
  Nevanlinna-extremal measures is formalized.
* The Hermite basis enters through the property that actually matters — it is a
  Hilbert basis indexed by `ℕ`, so its finite spans increase to a dense
  subspace.  No property of Hermite polynomials beyond completeness and
  orthonormality is used, and the results apply verbatim to any complete
  orthonormal basis.
-/

namespace BookProof.HermiteGalerkin

open BookProof.FarisLavine
open Filter Topology

/-! ## Step 2, general form: projections onto an increasing dense flag -/

section Flag

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]





end Flag

/-! ## The Galerkin flag of a Hilbert basis (the Hermite basis) -/

section Galerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The span of the first `m` basis vectors: the subspace the algorithm works in
at step `m`.  For the Hermite basis this is the space of polynomials of degree
`< m` times the Gaussian. -/
noncomputable def galerkinSpan (b : HilbertBasis ℕ ℂ F) (m : ℕ) : Submodule ℂ F :=
  Submodule.span ℂ (b '' {i | i < m})

instance galerkinSpan_finiteDimensional (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    FiniteDimensional ℂ (galerkinSpan b m) :=
  FiniteDimensional.span_of_finite ℂ ((Set.finite_Iio m).image _)





/-- **The finite-mode domain**: the span of all the basis vectors — the space of
all finite linear combinations of Hermite functions, which is where the matrix
elements `⟨Hermiteᵢ | H | Hermiteⱼ⟩` are computed. -/
noncomputable def finiteModeDomain (b : HilbertBasis ℕ ℂ F) : Submodule ℂ F :=
  Submodule.span ℂ (Set.range b)













/-- The **Galerkin (Rayleigh–Ritz) compression** `Pₘ A Pₘ` of a bounded operator
in the basis `b`: the `m × m` matrix the algorithm actually diagonalizes, read
back as an operator on the whole space. -/
noncomputable def galerkinCompression (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    F →L[ℂ] F :=
  (galerkinSpan b m).starProjection ∘L A ∘L (galerkinSpan b m).starProjection





end Galerkin

/-! ## Step 1 — the Rayleigh–Ritz connection: the compression carries the energy
form -/

section RayleighRitz

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]





variable {D : Submodule ℂ F}

/-- The set of **Ritz values** available at truncation level `V`: the energies
`⟪ψ, Hψ⟫` of the unit vectors `ψ` of `V`.  The algorithm's ground-state estimate
at that level is the infimum of this set. -/
def ritzSet (H : D →ₗ[ℂ] F) (V : Submodule ℂ F) : Set ℝ :=
  {t : ℝ | ∃ x : D, (x : F) ∈ V ∧ ‖(x : F)‖ = 1 ∧ t = quadForm H x}





/-- The **Ritz value** at truncation level `V`: the Rayleigh–Ritz minimum of the
energy over the unit sphere of `V`. -/
noncomputable def ritzInf (H : D →ₗ[ℂ] F) (V : Submodule ℂ F) : ℝ := sInf (ritzSet H V)









end RayleighRitz

/-! ## Step 3 — resolvents: strong resolvent convergence of the truncations -/

section Resolvent

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]











end Resolvent

/-! ## The two steps combined: what the algorithm selects -/

section Selection

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]









end Selection

/-! ## The hypotheses are not vacuous, and the domain is genuinely proper -/

section Examples

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The restriction of a bounded operator to the finite-mode (Hermite) domain:
the operator the algorithm sees, namely the matrix `⟨bᵢ | A₀ | bⱼ⟩`. -/
noncomputable def finiteModeRestrict (A₀ : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) :
    finiteModeDomain b →ₗ[ℂ] F :=
  A₀.toLinearMap.comp (finiteModeDomain b).subtype







end Examples

section ProperDomain

open scoped InnerProductSpace ENNReal lp

/-- The canonical Hilbert basis of `ℓ²(ℕ, ℂ)` — the abstract model of the
Hermite basis of `L²(ℝ)`. -/
noncomputable def ell2Basis : HilbertBasis ℕ ℂ (ℓ²(ℕ, ℂ)) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)



end ProperDomain

end BookProof.HermiteGalerkin


