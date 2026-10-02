-- Prove2me | Definitions.Def_ChapterElectroweakFieldStrength
-- name    : ChapterElectroweakFieldStrength
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:10:58.031993+00:00
-- url     : https://prove2.me/theorems/0b352e64-5266-4c2e-9597-c7c248b2128a
-- title:
--   Chapter ElectroweakFieldStrength
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterElectroweakFieldStrength.lean`): generated def bundle for ChapterElectroweakFieldStrength. See BookProof/ChapterElectroweakFieldStrength.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterElectroweakFieldStrength.lean

import Definitions.Def_ChapterParity
import Definitions.Def_ChapterParitySU2
import Mathlib


/-!
# Chapter "On the physical parity transformation and antiparticles" — the electroweak
`SU(2)_L` field strength via the trace projection

This file continues the finite algebraic core of the `book.tex` chapter *"On the physical
parity transformation and antiparticles"* (`book.tex` line ~7522, §"Majorana spinors in
the Standard Model").  The chapter records the electroweak field-strength tensors as
*trace projections* of the covariant-derivative commutator onto the Pauli generators:

  `W_{μν}^j = -\frac{i}{g}\,\mathrm{tr}([D_μ, D_ν]\,τ^j)
            = ∂_μ W_ν^j - ∂_ν W_μ^j - g\,ε^{jkl} W_μ^k W_ν^l`,
  `B_{μν}   = -\frac{i}{g'}\,\mathrm{tr}([D_μ, D_ν]\,σ_3) = ∂_μ B_ν - ∂_ν B_μ`,

with `D_μ = ∂_μ + i g W_μ^j τ_j/2 + …`.  The self-contained algebraic content — with the
partial derivatives abstracted as free "curvature" inputs — is a computation with the three
Pauli matrices `σ₁, σ₂, σ₃` (`ChapterParitySU2.pauliV`) and the totally antisymmetric
`ε^{jkl}` (`SU(2) ≅ su(2)` structure constants).  The physical modelling (the actual
space-time derivatives, the gauge fields as operator-valued distributions, the Lagrangian)
is left as prose.

Deliverables:

* `pauli_trace_orthonormal` : `tr(σ_a σ_b) = 2 δ_{ab}` — the generators are trace-orthogonal.
* `pauli_triple_trace` : `tr(σ_a σ_b σ_c) = 2 i ε_{abc}` — the closed form for the trace of
  a triple product (the source of the structure constants).
* `pauli_commutator` : `[σ_k, σ_l] = 2 i ∑_m ε_{klm} σ_m` — the `su(2)` commutation relations.
* `pauli_commutator_trace` : `tr([σ_k, σ_l] σ_j) = 4 i ε_{klj}`.
* `connection_comm_trace` : the trace projection of the quadratic (commutator) part of the
  curvature reproduces `i ∑_{k,l} ε_{klj} W_μ^k W_ν^l`.
* **`electroweak_fieldStrength`** (headline) : the full non-abelian trace-projection formula
  `-\frac{i}{g}\,\mathrm{tr}(F_{μν}\,σ^j) = G_j - g\,ε^{jkl} W_μ^k W_ν^l`, where `G_j` is the
  linear (curl) part `∂_μ W_ν^j - ∂_ν W_μ^j` and
  `F_{μν} = i g\,(∑_j G_j\,σ_j/2) + (i g)²\,[A_μ, A_ν]` is the `su(2)` curvature written
  from the covariant-derivative commutator `[D_μ, D_ν]`.
* **`abelian_fieldStrength`** (companion) : for a single abelian (`U(1)`) field the quadratic
  term drops out and the trace projection returns the pure curl `-\frac{i}{g}\,
  \mathrm{tr}(F_{μν}\,σ_3) = G` (`B_{μν} = ∂_μ B_ν - ∂_ν B_μ`).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open Matrix

namespace BookProof.ChapterElectroweakFieldStrength

open BookProof.ChapterParity BookProof.ChapterParitySU2

/-- The totally antisymmetric Levi-Civita symbol `ε_{ijk}` on `Fin 3` (as a complex number),
the `su(2)` structure constants. -/
def eps (i j k : Fin 3) : ℂ :=
  if i = 0 ∧ j = 1 ∧ k = 2 then 1
  else if i = 1 ∧ j = 2 ∧ k = 0 then 1
  else if i = 2 ∧ j = 0 ∧ k = 1 then 1
  else if i = 0 ∧ j = 2 ∧ k = 1 then -1
  else if i = 2 ∧ j = 1 ∧ k = 0 then -1
  else if i = 1 ∧ j = 0 ∧ k = 2 then -1
  else 0













/-- The `su(2)`-valued gauge connection `A = ∑_j W^j (σ_j / 2)` from the three real
component fields `W : Fin 3 → ℂ`. -/
noncomputable def connection (W : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ j, W j • ((1 / 2 : ℂ) • pauliV j)

/-- The `su(2)` field strength (curvature) written from the covariant-derivative commutator
`[D_μ, D_ν] = i g (∂_μ W_ν - ∂_ν W_μ)^j (σ_j/2) + (i g)² [A_μ, A_ν]`.  The linear (curl)
part `G_j = ∂_μ W_ν^j - ∂_ν W_μ^j` is given as an abstract input. -/
noncomputable def Fmat (g : ℂ) (G Wμ Wν : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I * g) • (∑ j, G j • ((1 / 2 : ℂ) • pauliV j))
    + (Complex.I * g) ^ 2 • (connection Wμ * connection Wν - connection Wν * connection Wμ)

/-- The book's trace projection `-\frac{i}{g}\,\mathrm{tr}(F σ^j)` extracting the `j`-th
field-strength component from an `su(2)`-valued curvature `F`. -/
noncomputable def proj (g : ℂ) (F : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 3) : ℂ :=
  (-Complex.I / g) * (F * pauliV j).trace







/-- The abelian curvature: a single `U(1)` field `B` along a fixed generator `σ_3` has the
form `i g G (σ_3 / 2)`, with **no quadratic term** because a matrix commutes with itself. -/
noncomputable def abelianFmat (g G : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I * g) • (G • ((1 / 2 : ℂ) • pauliV 2))



end BookProof.ChapterElectroweakFieldStrength


