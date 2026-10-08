-- Prove2me | Definitions.Def_ChapterF3
-- name    : ChapterF3
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T04:47:45.828986+00:00
-- url     : https://prove2.me/theorems/d1b066e2-b1c9-4944-bd94-1a004d4902cd
-- title:
--   Chapter F3
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterF3.lean`): generated def bundle for ChapterF3. See BookProof/ChapterF3.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterF3.lean

import Definitions.Def_ChapterF1
import Mathlib


/-!
# Chapter F3 — Quantum Flow Matching: Fock encoding & training (roadmap N14, §0 S7)

This file formalizes the algebraic / inner-product core of the *Quantum Flow
Matching* (QFM) algorithm (source `RiemannProof/QFM.tex`; reference
implementation `../unfer/qfm/`).  It follows §0 S7 of the roadmap (the
Mehler/Kopperman generative flow) and **reuses N12's number operator**
`BookProof.ChapterF1.numberOp` (`numberOp_monomial : N Xⁿ = n·Xⁿ`).

## Deliverables (this file)

* **F2.3 — orthogonal-Fock disjoint-support identities** (§5.1): packets with
  a.e.-disjoint supports have zero pointwise product (`disjoint_support_mul`,
  `disjoint_support_inner_zero`) — the "zero data loss" claim as a theorem.
* **F2.4 — diagonal-Gram closed-form training** (§5.2, the `O(M)` payoff):
  for a pairwise-orthogonal family `gⱼ`, the least-squares coefficients
  `αₖ = ⟪gₖ, b⟫/‖gₖ‖²` make the residual orthogonal to every `gₖ`
  (`diagonal_gram_residual_orthogonal`) — the defining property of the
  minimizer / orthogonal projection.
* **F2.6 — the vacuum projector `|0⟩⟨0|`** (§5.3): the rank-one map
  `projOnto ψ : s ↦ ⟪ψ, s⟫ • ψ` is idempotent for a unit `ψ`
  (`projOnto_idempotent`), self-adjoint (`projOnto_isSymmetric`), and equals the
  Mathlib orthogonal projection onto `ℂ ∙ ψ` (`projOnto_eq_starProjection`).
* **F2.7 — the diagonal generator's eigenstates** (§5.5): direct reuse of N12 —
  the vacuum `1` is annihilated (`diagGen_vacuum`) and the monomials `Xⁿ` are
  eigenvectors (`diagGen_eigenstate`) of `a·N̂`.
* **F2.8 — the Mehler overlap and the dressed-vacuum Bessel bound** (§6): the
  single-arc integral `mehler_arc_integral`, finite-product positivity of the
  overlaps `overlap_prod_pos`, and the key bound `Σⱼ εⱼ² ≤ 1`
  (`dressed_vacuum_bessel`) — exactly Bessel's inequality.
* **F2.9 — the Mehler projector as off-diagonal generator** (§5.3, §8): the
  channel matrix elements `⟪xᵢ, H₀ xⱼ⟫ = conj εᵢ · εⱼ` (`mehler_projector_matrix`).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); **no `EXTERNAL` hypothesis**.  Cites `../unfer` crates
`qfm/src/potential.rs`, `nested_fock_algebra` `ProjectVacuum`/`ProjectOnto`,
`qfm_hamiltonian`.
-/

open scoped BigOperators
open Polynomial

namespace BookProof.ChapterF3

noncomputable section

/-! ## F2.3 — orthogonal-Fock disjoint-support identities (`qfm/src/potential.rs`) -/

/-
**F2.3**: two functions with disjoint supports have zero pointwise product.
-/


/-
**F2.3** (L² orthogonality): packets with a.e.-disjoint supports are
orthogonal in `L²`, `∫ conj (f x) · g x ∂μ = 0`, since the integrand vanishes
pointwise.
-/


/-! ## F2.4 — the diagonal-Gram closed-form training solution (`O(M)` payoff) -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-
**F2.4**: for a pairwise-orthogonal family `g` of nonzero vectors, the
least-squares coefficients `αⱼ = ⟪gⱼ, b⟫/‖gⱼ‖²` (the per-coordinate closed form)
make the residual `b − Σⱼ αⱼ gⱼ` orthogonal to every `gₖ` — the normal
equations of the CFM training problem decouple, giving the `O(M)` solution.
-/


/-! ## F2.6 — the vacuum projector `|0⟩⟨0|` (`nested_fock_algebra` `ProjectVacuum`) -/

/-- The rank-one "project-onto-`ψ`" operator `s ↦ ⟪ψ, s⟫ • ψ`
(`../unfer` `ProjectOnto`). -/
def projOnto (ψ : E) : E →L[ℂ] E := (innerSL ℂ ψ).smulRight ψ

@[simp] theorem projOnto_apply (ψ s : E) : projOnto ψ s = (inner (𝕜 := ℂ) ψ s) • ψ := rfl

/-
**F2.6** (idempotency): for a unit vector `ψ`, `projOnto ψ` is idempotent
(`P ∘ P = P`) — the rank-1 projector shortcut.
-/


/-
**F2.6** (self-adjointness): `projOnto ψ` is symmetric,
`⟪projOnto ψ x, y⟫ = ⟪x, projOnto ψ y⟫`.
-/


/-
**F2.6** (identification with the Mathlib projection): for a unit `ψ`,
`projOnto ψ` is the orthogonal projection onto the line `ℂ ∙ ψ`.
-/


/-! ## F2.7 — the diagonal generator's eigenstates (direct N12 reuse) -/

/-
**F2.7** (vacuum): the diagonal generator `a·N̂` annihilates the vacuum
`|0⟩ = 1`.  (`N̂ 1 = 0`.)
-/


/-
**F2.7** (eigenstates): the monomials `Xⁿ = |xₙ⟩` are eigenvectors of the
diagonal generator `a·N̂` with eigenvalue `a·n` — direct reuse of N12's
`numberOp_monomial`.  Hence the Born populations are stationary (phase-only
evolution).
-/


/-! ## F2.8 — the Mehler overlap and the dressed-vacuum Bessel bound -/

/-
**F2.8** (single-arc overlap integral): integrating the constant Mehler
amplitude `√(1/w)·√(1/2π)` over an arc of angular width `w` gives `√(w/2π)`.
-/


/-
**F2.8** (positivity, the Kakutani-dichotomy point): a *finite* product of
strictly positive single-arc overlaps is strictly positive — the overlap
`εⱼ = ∏ᵢ √(w_{j,i}/2π) > 0`.  (An infinite product of `< 1` factors could
vanish; finiteness rules that out.)
-/


variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']

/-
**F2.8** (the dressed-vacuum Bessel bound `Σⱼ εⱼ² ≤ 1`): for an orthonormal
channel family `x : ι → E'` and a unit vacuum vector `v`, the overlaps
`εⱼ = ⟪xⱼ, v⟫` satisfy `Σⱼ ‖εⱼ‖² ≤ 1`.  This is exactly Bessel's inequality and
makes the dressed vacuum `c₀|vac⟩ + Σ εⱼ Bⱼ†|vac⟩` (with `c₀ = √(1−Σεⱼ²)`)
well-defined and unit-norm.
-/


/-! ## F2.9 — the Mehler projector as the off-diagonal generator -/

/-
**F2.9**: the channel matrix elements of the vacuum projector
`H₀ = |v⟩⟨v|` are `⟪xᵢ, H₀ xⱼ⟫ = conj(⟪v, xᵢ⟫) · ⟪v, xⱼ⟫ = conj εᵢ · εⱼ`
(with `εₖ = ⟪v, xₖ⟫`).  A one-line corollary of F2.6: the projector is by itself
an off-diagonal generator.
-/


end

end BookProof.ChapterF3


