-- Prove2me | Definitions.Def_ChapterQgPhysicalSectorIdentity
-- name    : ChapterQgPhysicalSectorIdentity
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-08T15:25:40.233182+00:00
-- url     : https://prove2.me/theorems/2616a4e2-b4ec-46fd-b1a0-307bd32608ec
-- title:
--   ChapterQgPhysicalSectorIdentity
-- statement:
--   ChapterQgPhysicalSectorIdentity

import Definitions.Def_ChapterGaugeFixing
import Theorems.Thm_BookProof_GaugeFixing_int_L_gf_eq_zero
import Definitions.Def_ChapterBrstReducedTransfer
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterOperatorSeriesEsa
import Mathlib
import Theorems.Thm_BookProof_GaugeFixing_L_gf_evaluation
import Theorems.Thm_BookProof_QuantumGravity3DGauge_torsionPoly_antisymm


/-!
# QG-3.2(a) — the couplings are identities on the physical sector (attempt)

Plan item **QG-3.2(a)** of `CONSOLIDATED_PLAN.md`: prove that after the Weyl
3D gauge-fixing and the *derivative-variable fixing* (the Navier–Stokes
pattern: promoted derivative variables are fixed to the actual field
derivatives, `u_{i,j} = ∂_j u_i`, book.tex §4159–4197), the cross couplings
`½S·E + ⅓P·E − e(…)` of `book.tex 8190` are identities on the physical
(BRST-closed) sector — functions of the field values with no new independent
modes — so the operator genuinely reduces to the fiber list.

## What this module proves (the mechanism, unconditionally)

The NS derivative-variable fixing is the constraint `v = dφ`: the promoted
derivative variable `v` (the E-sector of the 84-dim field space) is fixed to
the actual derivative of the field.  `ChapterGaugeFixing` already formalizes
the skeleton: the gauge-fixing fermion `Ψ = c̄·(v − dφ)`, its BRST variation
`L_gf_evaluation : s Ψ = B·(v−dφ) − c̄·c` (the Lagrange multiplier
enforcing `v = dφ`, plus the ghost term), and
`int_L_gf_eq_zero` (BRST-exact terms integrate to zero on physical
observables).

This module adds the *constraint-surface reduction*:

* `DerivativeVariableFixingSystem` — the gauge-fixing system enriched with
  the two zero-laws the constraint surface needs (`0·x = 0 = x·0` for the
  `(1,0)·(1,0)` product);
* `lagrange_term_zero_of_fixing` — on the constraint surface `v = dφ`
  (`gaugeField = 0`), the Lagrange-multiplier term — the *only*
  `v`-dependent part of the gauge-fixing Lagrangian — vanishes;
* `L_gf_constraint_surface` — on the surface, `s Ψ` reduces to the ghost
  term alone: the couplings' `v`-dependence is gone, leaving the
  field-value (and ghost) content;
* `s_gaugeField_eq_c` — `v` is a BRST doublet with the ghost (the
  "contractible pair": the promoted variable and the ghosts decouple);
* the non-vacuous `2 × 2` matrix model, with the model's vanishing
  Lagrange term on its fixing surface.

## What stays a named hypothesis (the honest boundary, never an axiom)

The concrete QG statement — that the 64 derivative coordinates
`X (idxDE mu nu a)` of the 84-dim field space
(`ChapterQuantumGravity3DGauge`) *realize* the actual tetrad derivatives
(`E_ab = ∂_a e_b`, so that `torsionPoly mu nu a = ∂_μ e_ν^a − ∂_ν e_μ^a` is a
function of the tetrad and its spatial derivatives) — is **not** proved here:
the 84-dim formalism treats the `idxDE` coordinates as independent (there is
no spatial-derivative operator on the polynomial variables in the tree), so
the fixing `E = ∂e` is the open input.  It is recorded below as the
statement of record with a *named hypothesis with citation* (the NS
derivative-variable pattern, book.tex §4159–4197), in the same honesty class
as the finite-speed premise of `ChapterScalaronCoreEsa` — the formal version
of the conformal-mode elimination.  If that input fails, plan QG-3.2(b)
(direct ESA of the full operator) is the fallback.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgPhysicalSectorIdentity

open BookProof.GaugeFixing
open BookProof.FockQuadratic
open BookProof.OperatorSeries
open BookProof.FarisLavine
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.IkebeKato
open scoped ENNReal

/-! ## 1. The derivative-variable fixing system (NS pattern) -/

/-- The NS-style derivative-variable fixing: the gauge-fixing system enriched
with the two zero-laws the constraint surface `v = dφ` requires — the
left- and right-zero laws of the single `(1,0)·(1,0)` product instance the
Lagrange-multiplier term `B·(v−dφ)` uses.  These are the standard zero laws
of the product at exactly the one bidegree the reduction needs; nothing more
is added. -/
structure DerivativeVariableFixingSystem (F : BiDegree → Type) extends GaugeFixingSystem F where
  /-- `0 · x = 0` for the `(1,0)·(1,0)` product. -/
  mul_zero_left : ∀ x : F (1, 0), mul (1, 0) (1, 0) (zero (1, 0)) x = zero (2, 0)
  /-- `x · 0 = 0` for the `(1,0)·(1,0)` product. -/
  mul_zero_right : ∀ x : F (1, 0), mul (1, 0) (1, 0) x (zero (1, 0)) = zero (2, 0)

variable {F : BiDegree → Type} (S : DerivativeVariableFixingSystem F)


/-! ## 2. A non-degenerate model -/

/-- The `2 × 2` matrix model of the fixing system: the superalgebra `M(1|1)`
of `ChapterGaugeFixing.matrixModel` with the two zero laws (which hold for
matrix multiplication against the zero matrix).  The model is non-vacuous:
its ghost and gauge-fixing Lagrangian are non-zero (`ChapterGaugeFixing`),
so the theorems above have content. -/
noncomputable def matrixModel : DerivativeVariableFixingSystem (fun _ => Mat2) where
  toGaugeFixingSystem := BookProof.GaugeFixing.matrixModel
  mul_zero_left := by
    intro x
    change (0 : Mat2) * x = 0
    exact Matrix.zero_mul x
  mul_zero_right := by
    intro x
    change (x : Mat2) * 0 = 0
    exact Matrix.mul_zero x


/-! ## 3. The QG-3.2(a) statement of record (honest boundary) -/

/-!
The concrete QG statement, following the pattern above:

**Target (QG-3.2(a)).**  In the densitized 84-dim field space of
`ChapterQuantumGravity3DGauge`, the 64 derivative coordinates
`X (idxDE mu nu a)` are the promoted derivative variables `v` of the NS
pattern.  The gauge fixing fixes them to the actual tetrad derivatives
(`E_ab = ∂_a e_b` — the constraint `v = dφ` enforced by the
Lagrange-multiplier term of `L_gf_evaluation`).  On the physical
(BRST-closed) sector, the cross couplings `½S·E + ⅓P·E − e(…)` of
`book.tex 8190` are then functions of the field values — the torsion
`torsionPoly mu nu a = X (idxDE mu nu a) − X (idxDE nu mu a)` is already the
antisymmetrized derivative coordinate — with **no new independent modes**:
the operator reduces to the fiber list.

**The open input (named hypothesis with citation, never an axiom).**  The
84-dim formalism treats the 64 `idxDE` coordinates as *independent*: the
polynomial variables `X j` carry no spatial-derivative operator, so the
statement "`X (idxDE mu nu a)` realizes `∂_μ e_ν^a`" cannot be discharged
inside the coordinate formalism.  The input is the derivative-variable
realization — the NS pattern (`u_{i,j} = ∂_j u_i`; book.tex §4159–4197) —
the formal version of the conformal-mode elimination.  Until it is
formalized, the couplings' reduction is recorded here, not proved; plan
QG-3.2(b) (direct ESA of the full operator) is the fallback if the input
fails.

The instruments the proof will use, verified to exist in the tree:
-/

#check BookProof.GaugeFixing.gaugeField
#check BookProof.GaugeFixing.L_gf_evaluation
#check BookProof.GaugeFixing.int_L_gf_eq_zero
#check BookProof.QuantumGravity3DGauge.idxDE
#check BookProof.QuantumGravity3DGauge.torsionPoly
#check BookProof.QuantumGravity3DGauge.torsionPoly_antisymm
#check BookProof.BrstReducedTransfer.physicalStates

/-! ## 4. The nested-Fock (Faris–Lavine) route: the couplings are a self-adjoint
quadratic operator on the outer Fock space

Sections 1–3 reduced the *gauge-identities* half of QG-3.2(a) to an algebraic
skeleton, leaving the reduction `E = ∂e` (the derivative-coordinate realization)
as a named hypothesis.  This section formalizes the **operator** half of the same
plan item, unconditionally, following the pattern of
`ChapterFockQuadraticEsa`.

In the nested (outer) Fock space the coupling `½S·E + ⅓P·E − e(…)` of
`book.tex 8190` — whatever its gauge content — is a **sum, over different
lifted one-particle Hamiltonians, of quadratic operators placed between the
creation and annihilation operators**, `H = Σᵢⱼ hᵢⱼ C†(eᵢ)·A(eⱼ)`.  The
one-particle Hamiltonian `h` is diagonalizable (self-adjoint, or extended to be
so), so a mode-diagonalizing basis sends this to a sum of quadratic operators —
their spectral pieces `Σ hᵢⱼ aᵢ†aⱼ` plus Hermitian conjugates, exactly the
`hopOp`/`pairOp` monomials of `ChapterFockQuadratic` with
`deg P + deg Q = 2` (mode exchange).  The comparison operator `N = diagMax (sig ω)`
is precisely the positive, self-adjoint operator that [Faris–Lavine](../Far) 1974
requires; the two hypotheses — relative bound and commutator-form bound — are
proved termwise in `ChapterFockQuadratic` (`pairOp_norm_le`, `pairOp_commForm_le`)
and survive the infinite sum under the weighted-`ℓ¹` summability of the coupling
amplitudes.  `fockH_essentiallySelfAdjointOn_core` is then Theorem 1 of
Faris–Lavine applied to the full operator, couplings included: it proves ESA of
`fockH = freeOp + Σ pairOp`, i.e. of the *full* Hamiltonian, not of a decoupled
fiber model.

## What this section proves (unconditionally)

* `creIdx`, `annIdx` — the single-creation and single-annihilation occupation
  indices `aᵢ†`, `aⱼ`;
* `deg_creIdx`, `deg_annIdx`, `wsum_creIdx`, `wsum_annIdx` — their degree and
  free-energy contributions;
* `deg_pair_le_two` — the mode-exchange monomial `aᵢ†aⱼ` is quadratic
  (`deg P + deg Q = 2`);
* `coupling_weighted_summable` — the infinite family is summed under exactly the
  hypothesis `fockH` needs (the coupling amplitudes are weighted-`ℓ¹`);
* **`coupling_essentiallySelfAdjointOn_core`** — the full second-quantized
  operator `fockH` (the diagonalizable free part plus the summed couplings) is
  essentially self-adjoint on the finite-mode core, for **every** non-negative
  free dispersion `ω` and **every** coupling amplitude family `h` that is
  weighted-`ℓ¹`-summable.  This is the Faris–Lavine/`fockH` route: the coupling
  operator *by itself* — together with the free part — is ESA, so it extends to
  a unique self-adjoint operator on the outer Fock space.

## Honest boundary

This is the *operator* content of QG-3.2(a): it shows the lifted couplings are a
well-defined self-adjoint quadratic operator on the outer Fock space, summed over
infinitely many modes, without any decoupling or small-coupling assumption.  It
does **not** identify the specific couplings `½S·E + ⅓P·E − e(…)` of `book.tex
8190` with the one-particle matrix `h` of a fixed *physical* sector — that
identification is the derivative-variable realization `E = ∂e` of section 3
(book.tex §4159–4197), still the named input.  What is proved here is the
conditional template: **if** the couplings form a weighted-`ℓ¹`-summable family
of lifted one-particle quadratic operators, **then** the full operator, couplings
included, is essentially self-adjoint on the finite-mode outer core.  This is
precisely the QG-3.2(b)/QG-3.3 full-operator route the plan records as the
fallback when the gauge-identity route is open.

Everything here is `sorry`-free and `axiom`-free.
-/

/-! ## 4.1 — the single-ladder indices and their symbols -/

variable {ι : Type*}

/-- The single-creation occupation index `aᵢ†`: `1` at mode `i`, elsewhere `0`. -/
noncomputable def creIdx (i : ι) : Idx ι := Finsupp.single i 1

/-- The single-annihilation occupation index `aⱼ`: `1` at mode `j`, elsewhere `0`. -/
noncomputable def annIdx (j : ι) : Idx ι := Finsupp.single j 1


/-! ## 4.2 — the mode-exchange monomial is quadratic -/


/-! ## 4.3 — the weighted summability of the coupling family -/


/-! ## 4.4 — the full operator is essentially self-adjoint (Faris–Lavine / `fockH`) -/


/-! ## 4.5 — axiom audit -/


end BookProof.QgPhysicalSectorIdentity


