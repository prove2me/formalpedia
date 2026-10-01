-- Prove2me | Definitions.Def_ChapterYangMillsAbelianNoGap
-- name    : ChapterYangMillsAbelianNoGap
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T11:18:47.431473+00:00
-- url     : https://prove2.me/theorems/b50210db-0155-472a-a6fb-63f4352b806c
-- title:
--   Chapter YangMillsAbelianNoGap
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterYangMillsAbelianNoGap.lean`): generated def bundle for ChapterYangMillsAbelianNoGap. See BookProof/ChapterYangMillsAbelianNoGap.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsAbelianNoGap.lean

import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterYangMillsHermite
import Mathlib


/-!
# The abelian gauge-fixed Yang–Mills Hamiltonian has **no** one-particle form gap

`BookProof.ChapterYangMillsFockGapChain` lifts a one-particle form gap
`⟪x, H₁ x⟫ ≥ μ‖x‖²` (`μ > 0`) on the Gauss–polynomial core to a nested-Fock mass gap for
`dΓ(H₁)`.  The form gap itself is a *hypothesis* there, stated for an arbitrary family of
structure constants `fabc`.

This chapter settles the hypothesis in the **abelian case** `fabc = 0`, and settles it
negatively: for `fabc = 0`

`H₁ = ½ Σ_m π_m² + ½ Σ_{i,a} B_{i a}²`,  `B_{i a} = Σ_{j k} ε_{ijk} ∂_j A_{k,a}`,

the momenta act only in the `24` field coordinates `A_{j,a}` while the potential is a
*linear* function of the `72` independent derivative coordinates, which carry no momentum at
all.  Widening the state in the field coordinates and narrowing it in the derivative
coordinates therefore costs nothing, and the infimum of the quadratic form over the core is
`0`:

* `exists_core_state_small_energy` — for every `ε > 0` there is a nonzero core state with
  `⟪x, H₁ x⟫ ≤ ε‖x‖²`;
* `ym_abelian_no_one_particle_form_gap` — consequently the one-particle form gap fails for
  every `μ > 0`.

The two states used are the squeezed states of `BookProof.ChapterSqueezedGaussStates`: a
*wide* one (`v → ½`, small momentum) in every field coordinate and a *narrow* one
(`v → −½`, small position) in every derivative coordinate.

**Scope.**  Nothing here is claimed about the physical, non-abelian case `fabc ≠ 0`: with
non-zero structure constants the magnetic potential `ε_{ijk}(∂_jA_{k,a} + f_{abc}A_{j,b}A_{k,c})`
couples the two groups of coordinates and the above cancellation is destroyed.  What the
result does show is that no proof of the one-particle form gap can be uniform in `fabc`: the
structure constants are *essential*, and the abelian instance of the conditional chain is
vacuous.
-/

namespace BookProof.YangMillsAbelianNoGap

open MvPolynomial MeasureTheory
open BookProof.HermiteProductCore BookProof.GaussCoordCombo BookProof.SqueezedGaussStates
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.HermiteGalerkin

noncomputable section

variable {d : ℕ}

/-! ## Real coefficients of the states -/









/-! ## The Gaussian normalisation constant -/





/-! ## Norms of core states from Gaussian integrals -/



/-! ## The product state -/

section ProductState

variable (vf : Fin d → ℝ) (Mf : Fin d → ℕ)

/-- The squeezed factor in the coordinate `j`. -/
def facW (j : Fin d) : MvPolynomial (Fin d) ℂ := squeezeState j (vf j) (Mf j)

/-- The Gaussian square norm of the factor in the coordinate `j`. -/
def facS (j : Fin d) : ℝ := coordComboSum (sqCoef (vf j) (Mf j)) 0 (Mf j)

/-- The product state: one squeezed factor per coordinate. -/
def bigP : MvPolynomial (Fin d) ℂ := ∏ j, facW vf Mf j























end ProductState

/-! ## The abelian Yang–Mills energy of the product state -/









/-- The parameter assignment: the *wide* squeezing parameter in the `3 + 24` spatial and field
coordinates, the *narrow* one in the `72` derivative coordinates. -/
def vsel (v₁ v₂ : ℝ) (j : Fin 99) : ℝ := if (j : ℕ) < 27 then v₁ else v₂

/-- The truncation order attached to each coordinate by `vsel`. -/
def Msel (M₁ M₂ : ℕ) (j : Fin 99) : ℕ := if (j : ℕ) < 27 then M₁ else M₂















end

end BookProof.YangMillsAbelianNoGap


