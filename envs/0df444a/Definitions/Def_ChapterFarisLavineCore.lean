-- Prove2me | Definitions.Def_ChapterFarisLavineCore
-- name    : ChapterFarisLavineCore
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T22:38:33.415255+00:00
-- url     : https://prove2.me/theorems/466aadfb-bc28-45a1-989f-8bf60b4e985f
-- title:
--   This module formalizes and **proves** the abstract theorem of
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.FarisLavineCore`, source chapter `BookProof/ChapterFarisLavineCore.lean`).
--
--   This module formalizes and **proves** the abstract theorem of
--
--   > W. G. Faris and R. B. Lavine, *Commutators and self-adjointness of Hamiltonian > operators*, Commun. Math. Phys. **35** (1974), 39–48, Theorem 1,
--
--   which elsewhere in this project (`BookProof.ChapterNavierStokesFlow`) had to be carried as a named hypothesis. The statement of the paper is:
--
--   > Let `H` be a Hermitian operator and `N ≥ 0` a positive self-adjoint operator > with (i) `𝒟(N) ⊆ 𝒟(H)` and (ii) `± i[H, N] ≤ c N` for some `c < ∞`. Then `H` > is essentially self-adjoint.
--
--   * The Hilbert space is a complex inner-product space `F` which is complete. * `H` and `N` are linear maps `D →ₗ[ℂ] F` on a common domain `D`, which plays the role of `𝒟(N)`; hypothesis (i) of the paper is built into this — `H` is defined wherever `N` is. (The conclusion is about the restriction of `H` to `𝒟(N)`, which by the last remark of §2 of the paper is the stronger statement: any symmetric extension of an essentially self-adjoint operator has the same closure.) * Symmetry is `SymmetricOn`, the quadratic form of `N` is `quadForm`, and `commForm H N x = ⟪x, i[H, N] x⟫` is the commutator form; that this is a real number is `commForm_eq`. Hypothesis (ii) is `|commForm H N x| ≤ c * quadForm N x`, which is exactly the two-sided bound `± i[H, N] ≤ c N` of the paper. * Essential self-adjointness is rendered, as everywhere in this project, by the vanishing of the deficiency spaces of the adjoint: `EssentiallySelfAdjointOn D H` says that no `w ≠ 0` satisfies `⟪H v, w⟫ = ⟪v, ± i w⟫` for all `v ∈ D`. * Self-adjointness of `N` is used in the paper at exactly one place: it makes `N + 1` a bijection of `𝒟(N)` onto the whole space, so that `(N+1)⁻¹ f` is an admissible test vector. That consequence — surjectivity of `N + 1` — is what is assumed here (`hNsurj`), so no spectral theory for unbounded operators is needed and the criterion applies verbatim to any `N` for which `-1` is in the resolvent set.
--
--   * `deficiencyTrivialAt_of_farisLavine` — the computation of the paper: under the Faris–Lavine hypotheses the deficiency space at `d i` vanishes whenever `2|d| > c`. This is the displayed inequality `± 2 d ⟪f, N⁻¹f⟫ ≤ c ⟪f, N⁻¹f⟫` of the original proof. * `exists_weak_graph_limit` — the closure of a symmetric operator with dense range of `H - d i` hits every vector: given `y`, there are `u, z` in the closure of the graph with `z - d i u = y`. Proved by hand from the identity `‖H x - d i x‖² = ‖H x‖² + d²‖x‖²`, which makes the approximating sequence and its image Cauchy. * `deficiencyTrivialAt_of_dense_range` — the classical basic criterion: for a symmetric operator, vanishing of the deficiency spaces at one conjugate pair `± d i` (`d ≠ 0`) forces vanishing at *every* non-real point. This is the step that upgrades the paper's "for `|d|` large" to essential self-adjointness. * `essentiallySelfAdjointOn_of_farisLavine` — **Theorem 1 of Faris–Lavine.** * `hasZeroDeficiencyOn_of_farisLavine` — the same conclusion in the predicate `BookProof.NavierStokesFlow.HasZeroDeficiencyOn` used by the Navier–Stokes chapters, for an operator that leaves its domain invariant. * `not_farisLavine_criterion_of_relative_bound` — a caveat, and the reason the hypotheses above are what they are: the *unrestricted* form of the criterion (relative bound `‖Hv‖ ≤ a‖Nv‖` plus commutator bound, with no positivity and no self-adjointness required of `N`) is **false**; taking `N = H` for the limit-circle Jacobi operator of `BookProof.ChapterNavierStokesDeficiency` satisfies both inequalities while essential self-adjointness fails. * `essentiallySelfAdjointOn_of_bounded_symmetric` and `multiplication_essentiallySelfAdjoint` — the hypotheses are satisfiable: the first in the everywhere-defined case, the second for the (unbounded) multiplication operator by an arbitrary real sequence on its ma
--
--   ...
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineCore.lean

import Mathlib

/-!
# The Faris–Lavine commutator criterion for essential self-adjointness

This module formalizes and **proves** the abstract theorem of

> W. G. Faris and R. B. Lavine, *Commutators and self-adjointness of Hamiltonian
> operators*, Commun. Math. Phys. **35** (1974), 39–48, Theorem 1,

which elsewhere in this project (`BookProof.ChapterNavierStokesFlow`) had to be
carried as a named hypothesis.  The statement of the paper is:

> Let `H` be a Hermitian operator and `N ≥ 0` a positive self-adjoint operator
> with (i) `𝒟(N) ⊆ 𝒟(H)` and (ii) `± i[H, N] ≤ c N` for some `c < ∞`.  Then `H`
> is essentially self-adjoint.

## How the statement is rendered here

* The Hilbert space is a complex inner-product space `F` which is complete.
* `H` and `N` are linear maps `D →ₗ[ℂ] F` on a common domain `D`, which plays the
  role of `𝒟(N)`; hypothesis (i) of the paper is built into this — `H` is defined
  wherever `N` is.  (The conclusion is about the restriction of `H` to `𝒟(N)`,
  which by the last remark of §2 of the paper is the stronger statement: any
  symmetric extension of an essentially self-adjoint operator has the same
  closure.)
* Symmetry is `SymmetricOn`, the quadratic form of `N` is `quadForm`, and
  `commForm H N x = ⟪x, i[H, N] x⟫` is the commutator form; that this is a real
  number is `commForm_eq`.  Hypothesis (ii) is `|commForm H N x| ≤ c * quadForm N x`,
  which is exactly the two-sided bound `± i[H, N] ≤ c N` of the paper.
* Essential self-adjointness is rendered, as everywhere in this project, by the
  vanishing of the deficiency spaces of the adjoint: `EssentiallySelfAdjointOn D H`
  says that no `w ≠ 0` satisfies `⟪H v, w⟫ = ⟪v, ± i w⟫` for all `v ∈ D`.
* Self-adjointness of `N` is used in the paper at exactly one place: it makes
  `N + 1` a bijection of `𝒟(N)` onto the whole space, so that `(N+1)⁻¹ f` is an
  admissible test vector.  That consequence — surjectivity of `N + 1` — is what
  is assumed here (`hNsurj`), so no spectral theory for unbounded operators is
  needed and the criterion applies verbatim to any `N` for which `-1` is in the
  resolvent set.

## Contents

* `deficiencyTrivialAt_of_farisLavine` — the computation of the paper: under the
  Faris–Lavine hypotheses the deficiency space at `d i` vanishes whenever
  `2|d| > c`.  This is the displayed inequality `± 2 d ⟪f, N⁻¹f⟫ ≤ c ⟪f, N⁻¹f⟫`
  of the original proof.
* `exists_weak_graph_limit` — the closure of a symmetric operator with dense
  range of `H - d i` hits every vector: given `y`, there are `u, z` in the closure
  of the graph with `z - d i u = y`.  Proved by hand from the identity
  `‖H x - d i x‖² = ‖H x‖² + d²‖x‖²`, which makes the approximating sequence and
  its image Cauchy.
* `deficiencyTrivialAt_of_dense_range` — the classical basic criterion: for a
  symmetric operator, vanishing of the deficiency spaces at one conjugate pair
  `± d i` (`d ≠ 0`) forces vanishing at *every* non-real point.  This is the step
  that upgrades the paper's "for `|d|` large" to essential self-adjointness.
* `essentiallySelfAdjointOn_of_farisLavine` — **Theorem 1 of Faris–Lavine.**
* `hasZeroDeficiencyOn_of_farisLavine` — the same conclusion in the predicate
  `BookProof.NavierStokesFlow.HasZeroDeficiencyOn` used by the Navier–Stokes
  chapters, for an operator that leaves its domain invariant.
* `not_farisLavine_criterion_of_relative_bound` — a caveat, and the reason the
  hypotheses above are what they are: the *unrestricted* form of the criterion
  (relative bound `‖Hv‖ ≤ a‖Nv‖` plus commutator bound, with no positivity and no
  self-adjointness required of `N`) is **false**; taking `N = H` for the
  limit-circle Jacobi operator of `BookProof.ChapterNavierStokesDeficiency`
  satisfies both inequalities while essential self-adjointness fails.
* `essentiallySelfAdjointOn_of_bounded_symmetric` and
  `multiplication_essentiallySelfAdjoint` — the hypotheses are satisfiable: the
  first in the everywhere-defined case, the second for the (unbounded)
  multiplication operator by an arbitrary real sequence on its maximal domain in
  `ℓ²(ℕ)`.

Nothing here is assumed: the module contains no `axiom`, and every result is
proved from Mathlib.
-/

namespace BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

/-! ## Basic notions -/

/-- `T` is symmetric (Hermitian) on the domain `D`: `⟪T x, y⟫ = ⟪x, T y⟫`. -/
def SymmetricOn (D : Submodule ℂ F) (T : D →ₗ[ℂ] F) : Prop :=
  ∀ x y : D, (inner ℂ (T x) (y : F) : ℂ) = inner ℂ (x : F) (T y)

/-- The deficiency space of the adjoint of `T` at `z` is trivial: the only `w`
with `⟪T v, w⟫ = ⟪v, z w⟫` for all `v` in the domain is `w = 0`.  Equivalently,
the range of `T - z̄` is dense. -/
def DeficiencyTrivialAt (D : Submodule ℂ F) (T : D →ₗ[ℂ] F) (z : ℂ) : Prop :=
  ∀ w : F, (∀ v : D, (inner ℂ (T v) w : ℂ) = z * inner ℂ (v : F) w) → w = 0

/-- **Essential self-adjointness** of a symmetric operator defined on `D`: both
deficiency spaces of the adjoint, at `i` and at `-i`, vanish. -/
def EssentiallySelfAdjointOn (D : Submodule ℂ F) (T : D →ₗ[ℂ] F) : Prop :=
  DeficiencyTrivialAt D T Complex.I ∧ DeficiencyTrivialAt D T (-Complex.I)

/-- The quadratic form `⟪x, N x⟫` of `N` (a real number when `N` is symmetric,
see `quadForm_im`). -/
noncomputable def quadForm (N : D →ₗ[ℂ] F) (x : D) : ℝ := (inner ℂ (x : F) (N x) : ℂ).re

/-- The commutator form `⟪x, i[H, N] x⟫ = i(⟪H x, N x⟫ - ⟪N x, H x⟫)`, which for
symmetric `H` and `N` is the quadratic form of the (formal) operator `i[H, N]`.
It is real: see `commForm_eq`. -/
noncomputable def commForm (H N : D →ₗ[ℂ] F) (x : D) : ℝ :=
  (Complex.I * ((inner ℂ (H x) (N x) : ℂ) - (inner ℂ (N x) (H x) : ℂ))).re









/-! ## The computation of Faris–Lavine

With `N` replaced by `N + 1` (which changes neither the commutator form, since
`⟪H x, x⟫` is real, nor the validity of the bound, since the form of `N` only
grows), the vector `g = (N+1)⁻¹ w` is admissible, and the deficiency identity at
`d i` reads `Im ⟪H g, (N+1) g⟫ = d ⟪g, (N+1) g⟫`.  The commutator bound turns
this into `2|d| t ≤ c t` with `t = ⟪g, (N+1)g⟫ ≥ ‖g‖²`, so `t = 0` as soon as
`2|d| > c`. -/



/-! ## From dense ranges at one conjugate pair to essential self-adjointness -/









/-! ## Theorem 1 of Faris–Lavine -/





/-! ## Corollary 1.1: the criterion on a core

The paper's Corollary 1.1 weakens the hypotheses to a linear subspace `C` which
is a core: the estimates are only required on `C`, and the conclusion is that the
restriction of `H` to `C` is already essentially self-adjoint.  Here the core
property is stated as it is used — every vector of `𝒟(N)` is approximated by
vectors of `C` *together with* their images under `N` (the graph norm of `N`) —
and the relative bound `‖Hf‖² ≤ a‖Nf‖² + b‖f‖²` transports the approximation from
the graph of `N` to the graph of `H`. -/





end BookProof.FarisLavine


