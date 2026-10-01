-- Prove2me | Definitions.Def_ChapterSmHiggsVacuum
-- name    : ChapterSmHiggsVacuum
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:52:36.547315+00:00
-- url     : https://prove2.me/theorems/21839590-e084-401c-b979-3be6821ee489
-- title:
--   Chapter SmHiggsVacuum
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSmHiggsVacuum.lean`): generated def bundle for ChapterSmHiggsVacuum. See BookProof/ChapterSmHiggsVacuum.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSmHiggsVacuum.lean

import Mathlib


/-!
# The Higgs vacuum: symmetry breaking as statics

The Standard-Model chapters of this project record, as an honest boundary, that **no
electroweak symmetry breaking as dynamics** is claimed: `V(φ)` and `D_iφ` are in the
one-particle operator, but no theorem selects the minimum `⟨φ⟩` or reads off masses.  This
module supplies the part of that statement which *is* a theorem about the potential of
`BookProof.ChapterSmHamiltonian` — the **statics** of symmetry breaking:

* `higgsV_sq_form` — the Mexican-hat identity
  `V(φ) = (λ/4)(‖φ‖² − μ²/λ)² − μ⁴/(4λ)`;
* `higgsV_ge_min` and `higgsV_eq_min_iff` — the potential is bounded below by `−μ⁴/(4λ)`,
  and the minimum is attained **exactly** on the vacuum manifold `‖φ‖² = μ²/λ = v²`: the
  vacuum is degenerate, which is what “broken symmetry” means at this level;
* `higgs_goldstone` — along any direction `w` orthogonal to a vacuum `u` the potential is
  *exactly* `V(u) + (λ/4)t⁴‖w‖⁴`: no quadratic term, i.e. the transverse directions are
  **massless Goldstone directions**;
* `higgs_radial` — along the radial direction the potential is exactly
  `V(u) + μ²‖u‖²t²(1 + t + t²/4)`, whose quadratic coefficient `μ²‖u‖²` is the curvature
  `½ m²‖u‖²` with `m² = 2μ²`: the **radial (Higgs) mode is massive**;
* `gaugeMassForm`, `gaugeMassForm_nonneg`, `gaugeMassForm_smul`,
  `gaugeMassForm_eq_zero_iff` — the covariant-derivative term evaluated at a constant vacuum
  is a positive-semidefinite quadratic form in the gauge fields which vanishes **exactly** on
  the generator combinations that annihilate the vacuum: broken generators acquire a mass
  term, unbroken ones stay massless.

## Honest boundary

These are statements about the potential and the covariant derivative at a fixed vacuum —
statics.  No time evolution of the broken phase, no expansion of the quantum Hamiltonian
around the vacuum, no physical particle spectrum and no measured value (of `v`, of a gauge
boson mass, or of any CKM/PMNS parameter) is claimed here.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmHiggsVacuum

open Finset

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The Higgs potential** `V(φ) = −½μ²‖φ‖² + ¼λ‖φ‖⁴` of §D6b-SM.1, as a function of the
real Higgs multiplet.  `mu2` is `μ²` and `lam` is `λ`. -/
def higgsV (lam mu2 : ℝ) (phi : E) : ℝ := -(mu2 / 2) * ‖phi‖ ^ 2 + (lam / 4) * ‖phi‖ ^ 4











/-! ## The gauge mass form at a vacuum -/

/-- **The gauge mass form** produced by a vacuum `u`: the covariant-derivative term
`½ Σ_i ‖X_i u‖²` of a constant Higgs configuration, for the generator combinations `X_i`
appearing in `D_i φ`.  It is the quadratic form in the gauge fields that the Higgs vacuum
adds to the Hamiltonian. -/
def gaugeMassForm (X : Fin 3 → Matrix (Fin 4) (Fin 4) ℝ) (u : Fin 4 → ℝ) : ℝ :=
  (1 / 2) * ∑ i : Fin 3, ∑ a : Fin 4, ((X i).mulVec u a) ^ 2







end

end BookProof.SmHiggsVacuum


