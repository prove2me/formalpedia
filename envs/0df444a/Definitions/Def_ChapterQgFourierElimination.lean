-- Prove2me | Definitions.Def_ChapterQgFourierElimination
-- name    : ChapterQgFourierElimination
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-27T04:59:34.330729+00:00
-- url     : https://prove2.me/theorems/fbbe55ff-d782-4fd0-af7b-0a6c012c5deb
-- title:
--   Chapter QgFourierElimination
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQgFourierElimination.lean`): generated def bundle for ChapterQgFourierElimination. See BookProof/ChapterQgFourierElimination.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgFourierElimination.lean

import Definitions.Def_ChapterQgBrstDerivativeGauge
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgVielbeinModeInstance
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Mathlib


/-!
# Fourier elimination of the derivative variables — the quantum-gravity vielbein sector

Item 7 of the quantum-gravity plan items of `CONSOLIDATED_PLAN.md`: the derivative modes of the
vielbein sector are **eliminated**, not gauge-fixed.  The gauge condition of
`BookProof/ChapterQgBrstDerivativeGauge.lean` reads `D_{μν}^i(k) = i k_μ e_ν^i(k)`; read as a
*substitution to be used when defining the operator*, it says that the auxiliary derivative
variables never have to exist: every torsion form is, from the start, a linear form in the
**physical** vielbein modes `CMode` alone.  (As everywhere in this thread the overall factor `i` of
the derivative symbol is a phase and is omitted; it cancels in the Gram matrix.)

What is proved here:

* `elimD` — the elimination `σ(D_{μν}^i(k)) = k_μ e_ν^i(k)` as a linear form on `CMode`, and
  `elimTorsion k mu nu i = elimD k mu nu i − elimD k nu mu i` — the torsion `T = D − Dᵀ` *after*
  the substitution.  Both have type `CMode → ℂ`: **the extended mode space `EMode` never appears**,
  neither in the definition nor in the domain of the operator built from it.
* `elimTorsion_eq_torsionCoef` — the eliminated torsion is exactly the physical Fourier torsion
  `k_μ e_ν^i − k_ν e_μ^i` at momentum `k` (and zero on the other momenta), so the substitution is
  lossless; `elimTorsion_eq_gaugeReduce` identifies it with the gauge-reduced extended form of the
  BRST chapter, which is how that chapter's two identities are *restated* as an elimination.
* `elimTorsion_antisymm`, `elimTorsion_diag`, `elimTorsion_conj` — the structural facts (the
  torsion is antisymmetric in the derivative indices, vanishes on the diagonal and is
  real-coefficient).
* `elimGram_eq_contTorsionGram` — the Gram matrix of *all* eliminated torsion forms is exactly the
  vielbein self-interaction `contTorsionGram` of the continuum model, with **no** hypothesis
  relating the two momenta (off the momentum diagonal both sides vanish).
* `qgElimModes` and `qgElim_esa` / `starobinsky_qgElim_esa` — consequently the mode data of the
  eliminated presentation is the continuum mode data (`qgElimModes_A` states that its
  self-interaction matrix *is* the eliminated Gram matrix), and the quantum-gravity Hamiltonian it
  defines is essentially self-adjoint on the outer Fock space, with the full exponential
  Einstein-frame scalaron wall and arbitrary coupling constant.  No BRST charge, no ghost sector
  and no restriction-to-a-subset argument is used: the physical torsion is the only torsion from
  the start.
* `elimConfig` and `formValue_dGauge_elimConfig` / `eq_elimConfig_of_gauge_fixed` — in the *full*
  vielbein–scalaron model of `ChapterQgVielbeinScalaronGaugeFL`, whose modes carry the nine
  vielbein components together with the twenty-seven derivative components, the elimination
  parameterizes the derivative-gauge constraint surface **exactly**: an eliminated configuration
  satisfies all twenty-seven constraints identically, and every configuration satisfying them is
  eliminated.  On that surface the torsion form is the exact Fourier torsion
  (`formValue_torsion_elimConfig`) and the 3D transverse form is unchanged
  (`formValue_gauge3d_elimConfig`).
* `elimTorsion_ne_zero` — the eliminated torsion is not the zero form, so the statement is not
  vacuous.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgFourierElim

open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgVielbeinModeInstance BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL

noncomputable section

/-! ## 1. The elimination of the derivative modes -/

/-- **The elimination** `σ(D_{μν}^i(k)) = k_μ e_ν^i(k)`: the auxiliary derivative variable is
replaced, *in the definition of the operator*, by the momentum weight times the vielbein mode.  The
result is a linear form on the physical modes `CMode` — the auxiliary mode space does not occur. -/
def elimD (k : Mom) (mu nu i : Fin 3) (z : CMode) : ℂ :=
  if z.1 = k then (if z.2 = (nu, i) then ((k mu : ℤ) : ℂ) else 0) else 0

/-- **The eliminated torsion** `T_{μν}^i = σ(D_{μν}^i) − σ(D_{νμ}^i)`. -/
def elimTorsion (k : Mom) (mu nu i : Fin 3) (z : CMode) : ℂ :=
  elimD k mu nu i z - elimD k nu mu i z











/-! ## 2. The vielbein self-interaction of the eliminated presentation -/

/-- **The Gram matrix of all eliminated torsion forms** — the vielbein self-interaction
`½ Σ_m T_m²` of the eliminated presentation. -/
def elimGram (x y : CMode) : ℂ :=
  ∑ mu : Fin 3, ∑ nu : Fin 3, ∑ i : Fin 3,
    (starRingEnd ℂ) (elimTorsion x.1 mu nu i x) * elimTorsion x.1 mu nu i y





/-! ## 3. The Hamiltonian of the eliminated presentation, and its essential self-adjointness -/

/-- **The mode data of the eliminated presentation.**  Its vielbein self-interaction is the Gram
matrix of the eliminated torsion forms (`qgElimModes_A`), and since that matrix *is*
`contTorsionGram`, the data is the continuum mode data — built on the physical modes only. -/
def qgElimModes (g : ℝ) : QgModeData CMode := qgContinuumModes g







/-! ## 4. The full vielbein–scalaron model: the elimination *is* the gauge surface

In the full model of `ChapterQgVielbeinScalaronGaugeFL` a mode carries `36` components per
momentum — the nine vielbein components `e_ν^i` **and** the twenty-seven derivative components
`D_{μν}^i` — and the derivative-gauge forms `G_{μν}^i = D_{μν}^i − i k_μ e_ν^i` cut out the
surface on which the latter are the derivatives of the former.  The elimination `elimConfig`
parameterizes exactly that surface by the nine vielbein components: every eliminated
configuration satisfies all twenty-seven constraints identically (`formValue_dGauge_elimConfig`),
and conversely every configuration satisfying them is an eliminated one
(`eq_elimConfig_of_gauge_fixed`).  On it the torsion form is the exact Fourier torsion
(`formValue_torsion_elimConfig`) and the 3D transverse gauge form is unchanged
(`formValue_gauge3d_elimConfig`).

Honest boundary: the Hamiltonian of that chapter is still *defined* on all `36` components, and
its essential self-adjointness (`qgFull_esa_farisLavine`) is the statement proved there; what is
added here is that the derivative components carry no independent content — the constraint surface
is the image of the elimination — so the eliminated presentation describes the same physics with
the nine vielbein components alone. -/

/-- The field-space components at one momentum: the nine vielbein components `e_ν^i`
(`Sum.inl`) and the twenty-seven independent derivative variables `D_{μν}^i`
(`Sum.inr`).  Inlined from `BookProof/ChapterQgVielbeinScalaronGaugeFL/Part1.lean`,
which has no def bundle of its own on the platform (an unpublished dep cannot be
imported, and the old `open BookProof.QgVielbeinScalaronGaugeFL` resolved nowhere). -/
abbrev Comp := (Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 3 × Fin 3)

/-- The vielbein component `e_ν^i`. -/
def eIdx (nu i : Fin 3) : Comp := Sum.inl (nu, i)

/-- The independent derivative variable `D_{μν}^i`, the coordinate representing the
spatial derivative `∂_μ e_ν^i`. -/
def dIdx (mu nu i : Fin 3) : Comp := Sum.inr (mu, nu, i)

/-- **The elimination on configurations of the full model**: the nine vielbein components are kept
and each derivative component is *defined* to be `i k_μ e_ν^i`. -/
def elimConfig (k : Mom) (z : Fin 3 × Fin 3 → ℂ) : Comp → ℂ
  | Sum.inl (nu, i) => z (nu, i)
  | Sum.inr (mu, nu, i) => Complex.I * ((k mu : ℤ) : ℂ) * z (nu, i)

@[simp] theorem elimConfig_e (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (nu i : Fin 3) :
    elimConfig k z (eIdx nu i) = z (nu, i) := rfl

@[simp] theorem elimConfig_d (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (mu nu i : Fin 3) :
    elimConfig k z (dIdx mu nu i) = Complex.I * ((k mu : ℤ) : ℂ) * z (nu, i) := rfl









/-! ## 5. Non-vacuity -/



end

end BookProof.QgFourierElim


