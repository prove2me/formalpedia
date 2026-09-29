-- Prove2me | Definitions.Def_ChapterNavierStokesFarisLavineLift
-- name    : ChapterNavierStokesFarisLavineLift
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T11:31:09.361268+00:00
-- url     : https://prove2.me/theorems/f6766a7b-51c0-4c5a-9551-ade12db6bf38
-- title:
--   Companion to `BookProof.ChapterNavierStokesSecondQuant`, which lifts *essential self-adjointness* from the sectors of a ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesFarisLavineLift`, source chapter `BookProof/ChapterNavierStokesFarisLavineLift.lean`).
--
--   Companion to `BookProof.ChapterNavierStokesSecondQuant`, which lifts *essential self-adjointness* from the sectors of a Fock space to the finite-particle domain. This module supplies the other two ingredients of the Faris–Lavine route to essential self-adjointness of the Navier–Stokes Hamiltonian:
--
--   **1. The one-particle comparison operator.** In the fiber space the advection term is a *linear* vector field `V(u)`, so the natural comparison operator is `n = ∑ᵢ πᵢ² + ∑ᵢ Vᵢ² + I`. `ComparisonData` packages the (symmetric) momenta `πᵢ` and drifts `Vᵢ` on a dense domain of an arbitrary complex inner product space, and `ComparisonData.comparison` is the operator. Proved here: `comparison_isSymmetricDom` (symmetry), `comparison_inner_eq` (the quadratic form is `∑‖πᵢv‖² + ∑‖Vᵢv‖² + ‖v‖²` — no cross terms, because the squares are squares of symmetric operators), `comparison_ge_norm_sq` (`n ≥ I`, the positivity Faris–Lavine asks of the comparison operator) and two criteria for essential self-adjointness: `comparison_hasZeroDeficiencyOn_of_eigenvectors` from a total family of eigenvectors, and `diagComparison_hasZeroDeficiencyOn`, an unconditional instance in the representation in which the `πᵢ` and `Vᵢ` are simultaneously diagonal (the fiber momentum representation), where the operator is also genuinely unbounded (`diagComparison_not_bounded`).
--
--   **2. How the two Faris–Lavine bounds behave when summed over particles.** On an `m`-particle sector the second-quantized operators are `Ĥ = ∑ₖ hₖ` and `N̂ = ∑ₖ nₖ + I`.
--
--   * `norm_sum_le_of_pairwise` — the *operator* bound lifts with the **same** constant provided the domination holds *pairwise*, `|Re⟪hₖv, hₗv⟫| ≤ c² Re⟪nₖv, nₗv⟫` for all pairs `k, l`. * `not_forall_norm_sum_le_of_pointwise` — and pairwise is genuinely needed: the naive argument "triangle inequality plus the one-particle bound" is **not** valid. There are two pairs `(hₖ, nₖ)` with `‖hₖ x‖ ≤ ‖nₖ x‖` for every `x` and yet `‖(h₀ + h₁)x‖ > ‖(n₀ + n₁)x‖`; the step `∑ₖ ‖nₖ Ψ‖ ≤ ‖N̂ Ψ‖` in the informal argument is false as stated. * `abs_re_inner_commutator_sum_le` — the *form commutator* bound, by contrast, lifts exactly as the informal argument says, because quadratic forms are additive: with `[hₖ, nₗ] = 0` for `k ≠ l` (different particles) one has `[Ĥ, N̂] = ∑ₖ [hₖ, nₖ]`(`commDom_sum`, `commDom_add_id`) and therefore `|Re⟪Ψ, [Ĥ, N̂]Ψ⟫| ≤ c₂ Re⟪Ψ, N̂Ψ⟫`.
--
--   Nothing here claims essential self-adjointness of the continuum Navier–Stokes generator. The Faris–Lavine criterion itself is not proved anywhere in this project; it enters as a named hypothesis (`ns_esa_of_farisLavine_dense`). What is established here is exactly which bounds survive second quantization, and in what form.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFarisLavineLift.lean

import Definitions.Def_ChapterNavierStokesFullEsa
import Mathlib

import Mathlib

/-!
# The one-particle comparison operator, and how the Faris–Lavine bounds lift

Companion to `BookProof.ChapterNavierStokesSecondQuant`, which lifts *essential
self-adjointness* from the sectors of a Fock space to the finite-particle
domain.  This module supplies the other two ingredients of the Faris–Lavine
route to essential self-adjointness of the Navier–Stokes Hamiltonian:

**1. The one-particle comparison operator.**  In the fiber space the advection
term is a *linear* vector field `V(u)`, so the natural comparison operator is
`n = ∑ᵢ πᵢ² + ∑ᵢ Vᵢ² + I`.  `ComparisonData` packages the (symmetric) momenta
`πᵢ` and drifts `Vᵢ` on a dense domain of an arbitrary complex inner product
space, and `ComparisonData.comparison` is the operator.  Proved here:
`comparison_isSymmetricDom` (symmetry), `comparison_inner_eq` (the quadratic
form is `∑‖πᵢv‖² + ∑‖Vᵢv‖² + ‖v‖²` — no cross terms, because the squares are
squares of symmetric operators), `comparison_ge_norm_sq` (`n ≥ I`, the
positivity Faris–Lavine asks of the comparison operator) and two criteria for
essential self-adjointness: `comparison_hasZeroDeficiencyOn_of_eigenvectors`
from a total family of eigenvectors, and `diagComparison_hasZeroDeficiencyOn`,
an unconditional instance in the representation in which the `πᵢ` and `Vᵢ` are
simultaneously diagonal (the fiber momentum representation), where the operator
is also genuinely unbounded (`diagComparison_not_bounded`).

**2. How the two Faris–Lavine bounds behave when summed over particles.**  On an
`m`-particle sector the second-quantized operators are `Ĥ = ∑ₖ hₖ` and
`N̂ = ∑ₖ nₖ + I`.

* `norm_sum_le_of_pairwise` — the *operator* bound lifts with the **same**
  constant provided the domination holds *pairwise*,
  `|Re⟪hₖv, hₗv⟫| ≤ c² Re⟪nₖv, nₗv⟫` for all pairs `k, l`.
* `not_forall_norm_sum_le_of_pointwise` — and pairwise is genuinely needed: the
  naive argument "triangle inequality plus the one-particle bound" is **not**
  valid.  There are two pairs `(hₖ, nₖ)` with `‖hₖ x‖ ≤ ‖nₖ x‖` for every `x`
  and yet `‖(h₀ + h₁)x‖ > ‖(n₀ + n₁)x‖`; the step
  `∑ₖ ‖nₖ Ψ‖ ≤ ‖N̂ Ψ‖` in the informal argument is false as stated.
* `abs_re_inner_commutator_sum_le` — the *form commutator* bound, by contrast,
  lifts exactly as the informal argument says, because quadratic forms are
  additive: with `[hₖ, nₗ] = 0` for `k ≠ l` (different particles) one has
  `[Ĥ, N̂] = ∑ₖ [hₖ, nₖ]`(`commDom_sum`, `commDom_add_id`) and therefore
  `|Re⟪Ψ, [Ĥ, N̂]Ψ⟫| ≤ c₂ Re⟪Ψ, N̂Ψ⟫`.

## Scope

Nothing here claims essential self-adjointness of the continuum Navier–Stokes
generator.  The Faris–Lavine criterion itself is not proved anywhere in this
project; it enters as a named hypothesis (`ns_esa_of_farisLavine_dense`).  What
is established here is exactly which bounds survive second quantization, and in
what form.
-/

namespace BookProof.NavierStokesFlow

namespace FarisLavineLift

open FullEsa

/-! ## Elementary inner-product facts -/

section Elementary

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]





end Elementary

/-! ## The one-particle comparison operator `n = π² + V² + I` -/

section Comparison

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The data of a one-particle comparison operator on a fiber space: a dense
domain, the momenta `πᵢ = -i ∂/∂uᵢ` and the drifts `Vᵢ(u)`, all symmetric and
preserving the domain.  In the Navier–Stokes fiber space `Vᵢ(u) = u_{i,j}u_j −
ν u_{i,jj}` is a *linear* function of the (independent) fiber coordinates, so
`Vᵢ²` is a non-negative quadratic potential. -/
structure ComparisonData (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (d : ℕ) where
  /-- The dense domain (a core: in the Navier–Stokes fiber space, `C_c^∞`). -/
  D : Submodule ℂ F
  /-- The domain is dense. -/
  dense : Dense (D : Set F)
  /-- The momenta. -/
  mom : Fin d → (D →ₗ[ℂ] D)
  /-- The drift (advection) fields. -/
  drift : Fin d → (D →ₗ[ℂ] D)
  /-- Each momentum is symmetric. -/
  mom_symm : ∀ i, IsSymmetricDom (mom i)
  /-- Each drift is symmetric. -/
  drift_symm : ∀ i, IsSymmetricDom (drift i)

namespace ComparisonData

variable {d : ℕ} (c : ComparisonData F d)

/-- The comparison operator `n = ∑ᵢ πᵢ² + ∑ᵢ Vᵢ² + I`. -/
noncomputable def comparison : c.D →ₗ[ℂ] c.D :=
  (∑ i, (c.mom i).comp (c.mom i)) + (∑ i, (c.drift i).comp (c.drift i)) + LinearMap.id











end ComparisonData

end Comparison

/-! ### An unconditional instance: the comparison operator in the momentum
representation -/

section DiagonalComparison

open LpNat DiagonalEsa

/-- The comparison operator in the representation in which the momenta `πᵢ` and
the drifts `Vᵢ` are simultaneously diagonal — the fiber momentum representation,
where `πᵢ` is multiplication by the momentum symbol `pᵢ` and `Vᵢ` multiplication
by the (linear) advection symbol `qᵢ`.  Here `ℓ²(ℕ)` plays the role of the fiber
space and the finite-mode states the role of the core `C_c^∞`. -/
noncomputable def diagComparisonData (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    ComparisonData L2N d where
  D := lpFiniteModes ℕ
  dense := lpFiniteModes_dense
  mom i := diagOp (p i)
  drift i := diagOp (q i)
  mom_symm _ := FullEsa.diagOp_isSymmetricDom _
  drift_symm _ := FullEsa.diagOp_isSymmetricDom _









end DiagonalComparison

/-! ## Lifting the two Faris–Lavine bounds over the particles of a sector -/

section Lifting

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}







/-! ### The commutator -/

/-- The commutator of two domain-preserving operators. -/
def commDom (A B : D →ₗ[ℂ] D) : D →ₗ[ℂ] D := A.comp B - B.comp A











end Lifting

/-! ## Sharpness: the naive lifting of the operator bound is invalid -/

section Sharpness

open EuclideanSpace

/-- The two-dimensional fiber used for the counterexample. -/
abbrev E2 := EuclideanSpace ℂ (Fin 2)

/-- `hₖ x = xₖ · e₀`: both "particles" push into the same direction. -/
noncomputable def hEx (k : Fin 2) : E2 →ₗ[ℂ] E2 :=
  LinearMap.smulRight (EuclideanSpace.projₗ (𝕜 := ℂ) k)
    (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))

/-- `nₖ x = xₖ · eₖ`: the comparison operators are the coordinate
projections. -/
noncomputable def nEx (k : Fin 2) : E2 →ₗ[ℂ] E2 :=
  LinearMap.smulRight (EuclideanSpace.projₗ (𝕜 := ℂ) k) (EuclideanSpace.single k (1 : ℂ))





/-- The state on which the naive lifting fails: both coordinates equal to 1. -/
noncomputable def vEx : E2 :=
  EuclideanSpace.single (0 : Fin 2) (1 : ℂ) + EuclideanSpace.single (1 : Fin 2) (1 : ℂ)











end Sharpness

end FarisLavineLift

end BookProof.NavierStokesFlow


