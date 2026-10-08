-- Prove2me | Definitions.Def_ChapterFockFieldPerturbation
-- name    : ChapterFockFieldPerturbation
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-08T12:32:02.448404+00:00
-- url     : https://prove2.me/theorems/9d8483f7-150c-4d79-b29d-f0fa3d4657e5
-- title:
--   Chapter FockFieldPerturbation
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFockFieldPerturbation.lean`): generated def bundle for ChapterFockFieldPerturbation. See BookProof/ChapterFockFieldPerturbation.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFockFieldPerturbation.lean

import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Mathlib


/-!
# Chapter FockFieldPerturbation — an *unbounded* number-changing perturbation

`CONSOLIDATED_PLAN.md`, status update 2026-08-28c, records the exact boundary reached by
`ChapterFockInteractionStability`: a gap survives an arbitrary **bounded** number-changing
perturbation, and the relatively-form-bounded statement
`gap_persists_of_relative_form_bound` is "the shape in which a claim for an unbounded
interaction could be made, but supplying the domination `|v| ≤ a q + b‖·‖²` for the physical
interaction is not done here".

This chapter supplies such a domination for a genuinely unbounded, genuinely
number-changing operator: the **field operator**

  `Φ(f) = a†(f) + a(f)`,

the linear (Yukawa-type) coupling of the Fock field to a one-particle vector `f`.  `Φ(f)` is
not a bounded operator on Fock space (`fieldVec_unbounded`) and it does not commute with the
number operator (`fieldVec_vac`), so neither the bounded corollaries of
`ChapterFockInteractionStability` nor the number-preserving lift of
`ChapterFockNumberPreservingGap` applies to it.

## Deliverables

* `annVec` — the annihilation operator `a(f) = Σ_j conj(f_j) a_j` of a one-particle vector,
  adjoint to the project's `creVec` (`inner_creVec_annVec`);
* `numberQuad` — the number quadratic form `⟪u, N u⟫`, and `numberQuad_eq_sum`:
  `⟪u, N u⟫ = Σ_k ‖a_k u‖²`;
* **`norm_annVec_le`** — the `N^{1/2}` estimate `‖a(f) u‖ ≤ ‖f‖ ⟪u, N u⟫^{1/2}`, by
  Cauchy–Schwarz over the modes;
* **`abs_re_inner_fieldVec_le`** — `|Re⟪u, Φ(f) u⟫| ≤ 2‖f‖ ⟪u, N u⟫^{1/2}‖u‖`;
* **`fieldVec_relative_form_bound`** — the domination the plan asks for:
  `|Re⟪u, Φ(f) u⟫| ≤ (t/μ)·Re⟪u, dΓ(h) u⟫ + (‖f‖²/t)‖u‖²` for every `t > 0`, whenever the
  one-particle Hamiltonian satisfies `h − μ ≥ 0` with `μ > 0`;
* **`fock_gap_of_field_perturbation`** — the conclusion: with a one-particle gap `h ≥ μ` and
  `‖f‖ ≤ μ`, every vacuum-orthogonal finite-particle state has `dΓ(h) + Φ(f)` energy at
  least `(μ − 2‖f‖)‖u‖²`; `fock_gap_of_field_perturbation_pos` records when this is
  strictly positive;
* `fieldVec_unbounded` — `Φ(f)` really is unbounded, so this is not a corollary of the
  bounded theory.

## Honest boundary

`Φ(f)` is linear in the creation/annihilation operators; it changes the particle number by
one.  Yang–Mills interaction terms are cubic and quartic in the field and are *not* covered
by this chapter.  What is proved is that the certificate chain's one-particle gap survives a
concrete unbounded number-changing coupling, quantitatively, with the explicit smallness
condition `2‖f‖ < μ`.  `1.932` remains a certified truncated number; no mass gap of the
physical Hamiltonian is claimed.

Everything is `sorry`-free and introduces no axioms.
-/

noncomputable section

namespace BookProof.FockFieldPerturbation

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability

/-! ## 1. The annihilation operator of a one-particle vector -/

/-- The `ℓ²` norm of a finitely supported one-particle vector. -/
def l2norm (f : ℕ →₀ ℂ) : ℝ := Real.sqrt (∑ j ∈ f.support, ‖f j‖ ^ 2)

/-- **The annihilation operator** `a(f) = Σ_j conj(f_j) a_j` of a one-particle vector `f`,
the adjoint of the project's creation operator `creVec f = a†(f)`. -/
def annVec (f : ℕ →₀ ℂ) : FockAlg →ₗ[ℂ] FockAlg :=
  ∑ j ∈ f.support, ((starRingEnd ℂ) (f j)) • annA j

/-- **The field operator** `Φ(f) = a†(f) + a(f)`. -/
def fieldVec (f : ℕ →₀ ℂ) : FockAlg →ₗ[ℂ] FockAlg := creVec f + annVec f

/-- The number quadratic form `⟪u, N u⟫`. -/
def numberQuad (u : FockAlg) : ℝ :=
  (inner ℂ (toLp u) (toLp (dGamma numberCol u)) : ℂ).re









/-! ## 2. The number form is the sum of the mode annihilations -/









/-! ## 3. The `N^{1/2}` estimate -/







/-! ## 4. The relative form bound -/







/-! ## 5. The gap under the unbounded perturbation -/





/-! ## 6. The perturbation is genuinely unbounded and genuinely number-changing -/





/-! ## 7. Axiom audit -/

section Audit

-- The audited declarations live in this chapter's `Theorems.Thm_*` stubs, which
-- import this bundle back: the bundle cannot import them (cycle), and none of
-- the names is declared here, so every `#print axioms` line was an
-- `Unknown constant` server FAILED.  Audit dropped (2026-10-08, §5d).

end Audit

end BookProof.FockFieldPerturbation

end


