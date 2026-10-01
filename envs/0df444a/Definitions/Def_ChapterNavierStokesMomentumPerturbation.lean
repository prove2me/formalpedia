-- Prove2me | Definitions.Def_ChapterNavierStokesMomentumPerturbation
-- name    : ChapterNavierStokesMomentumPerturbation
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:30:49.584712+00:00
-- url     : https://prove2.me/theorems/39683fa2-9df6-4391-be0d-68e0982acb11
-- title:
--   Chapter NavierStokesMomentumPerturbation
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesMomentumPerturbation.lean`): generated def bundle for ChapterNavierStokesMomentumPerturbation. See BookProof/ChapterNavierStokesMomentumPerturbation.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesMomentumPerturbation.lean

import Definitions.Def_ChapterNavierStokesIkebeKato
import Mathlib


/-!
# A non-commuting Hamiltonian to which the criterion applies

`BookProof.ChapterNavierStokesIkebeKato` proves that a symmetric operator `H` on
the maximal domain of the comparison operator `N` (multiplication by a
non-negative momentum symbol) is essentially self-adjoint on the finite-mode core
as soon as it satisfies the two Faris–Lavine inequalities.  This module verifies
that those hypotheses are met by a genuinely **unbounded** Hamiltonian whose
commutator with `N` does **not** vanish, so the criterion is not applied
vacuously:

`H = N + B`, where `B x = ⟪u, x⟫ w + ⟪w, x⟫ u` is the symmetric rank-`≤ 2`
operator built from two states `u, w` of the maximal domain.

* `rankTwo_symmetric`, `rankTwo_norm_le` — `B` is symmetric and bounded by
  `2‖u‖‖w‖`;
* `pertHam_symmetricOn`, `pertHam_relative_bound`, `pertHam_commForm_bound` — the
  two Faris–Lavine inequalities, the second one because
  `⟪w, N x⟫ = ⟪N w, x⟫` for `w` in the maximal domain, so the commutator form is
  bounded by a multiple of `‖x‖² ≤ ⟪x, N x⟫`;
* `pertHam_essentiallySelfAdjointOn_core` — hence `N + B` is essentially
  self-adjoint on the finite-mode core;
* `exists_commForm_ne_zero` — and the commutator form of the pair really is
  non-zero: with the symbol `c(k) = k + 1` and `u = e₀`, `w = e₁` one has
  `⟪x, i[H, N] x⟫ = −2` at `x = e₀ + i e₁`.
-/

namespace BookProof.NavierStokesFlow

namespace MomentumPerturbation

open LpNat FarisLavine IkebeKato

variable {ι : Type*}

/-! ## The symmetric rank-two perturbation -/

/-- The symmetric rank-`≤ 2` operator `B x = ⟪u, x⟫ w + ⟪w, x⟫ u`. -/
noncomputable def rankTwo (u w : L2I ι) : L2I ι →ₗ[ℂ] L2I ι where
  toFun x := (inner ℂ u x : ℂ) • w + (inner ℂ w x : ℂ) • u
  map_add' x y := by
    simp only [inner_add_right, add_smul]
    abel
  map_smul' a x := by
    simp only [inner_smul_right, smul_smul, RingHom.id_apply, smul_add]







/-! ## The perturbed Hamiltonian `H = N + B` -/

/-- The perturbed Hamiltonian `H = N + B` on the maximal domain of `N`. -/
noncomputable def pertHam (c : ι → ℝ) (u w : L2I ι) : maxDom c →ₗ[ℂ] L2I ι :=
  diagMax c + (rankTwo u w).comp (maxDom c).subtype











/-! ## The commutator really does not vanish -/

section Witness

/-- The symbol `c(k) = k + 1`: unbounded, and `≥ 1`. -/
def linSymbol : ℕ → ℝ := fun k => (k : ℝ) + 1



/-- The two states of the perturbation, and the test state. -/
noncomputable def eState (k : ℕ) : L2I ℕ := lp.single 2 k (1 : ℂ)



noncomputable def testState : L2I ℕ := lp.single 2 0 (1 : ℂ) + lp.single 2 1 Complex.I

















end Witness

end MomentumPerturbation

end BookProof.NavierStokesFlow


