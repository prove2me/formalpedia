-- Prove2me | Definitions.Def_ChapterScalaronFockEsa
-- name    : ChapterScalaronFockEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T17:09:49.350577+00:00
-- url     : https://prove2.me/theorems/1f4cec8f-c13b-4216-a0c1-d21a5460e78a
-- title:
--   The Lean 4 theorem `contDiff_qgManyPotential` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterScalaronFockEsa.lean`): generated def bundle for ChapterScalaronFockEsa. See BookProof/ChapterScalaronFockEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronFockEsa.lean

import Theorems.Thm_BookProof_ScalaronEsa_contDiff_scalaronFullPotential

import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Mathlib


/-!
# From one particle to the nested Fock space: the scalaron Hamiltonian in the continuum

Plan item **A5** (`CONSOLIDATED_PLAN.md` §10.5), closing step.  `ChapterScalaronCoreEsa`
proved essential self-adjointness of the gauge-fixed `R + αR²` Hamiltonian — conformal mode
plus the Einstein-frame **Starobinsky scalaron potential**, exponential wall and all — on a
dense core of the *one-particle* Hilbert space.  `ChapterDirectSumEsa` proved that essential
self-adjointness is fibrewise: a deficiency vector of an orthogonal direct sum, tested
against single-fibre states, has vanishing coordinates.

The state space of the quantised theory is a **nested Fock space** `⊕ₙ L²(Eₙ)`: the
`n`-particle sector carries the `n`-fold configuration space, and the Hamiltonian acts
sector by sector, the `n`-particle potential being the sum of the one-particle potentials of
the individual quanta.  This module links the two proved theorems and states the conclusion
on the Fock space itself.

## What is proved

**1. The generic instrument.**  For an arbitrary family `E : ℕ → Type*` of finite-dimensional
configuration sectors and an arbitrary family of *smooth* real potentials `W n : E n → ℝ` —
no growth, no boundedness, no semiboundedness — the operator `⊕ₙ W n` on the algebraic
direct sum `nestedCore` of the compactly supported smooth sector cores is densely defined
(`nestedCore_dense`), symmetric (`fockSmoothPotential_symmetric`), has trivial deficiency at
every non-real point (`fockSmoothPotential_deficiencyTrivialAt`), is essentially
self-adjoint (`fockSmoothPotential_esa`) and generates the complete unitary group
(`fockSmoothPotential_stone_flow`).

**2. The many-body scalaron potential.**  On the `n`-particle sector
`qgSector n = ℝ^(n × 2)` — each quantum carrying a conformal mode `R_c` and a scalaron `φ` —
the many-body gauge-fixed potential `∑ⱼ (V₃(R_c ⱼ) + V(φ ⱼ))` is smooth
(`contDiff_qgManyPotential`), bounded below by `−n·M⁴/(16α)` (`qgManyPotential_ge`) and
essentially self-adjoint on the sector core (`qgManyPotential_esa`).  At `n = 1` it *is* the
one-particle potential of `ChapterScalaronCoreEsa` (`qgManyPotential_one`).

**3. The Fock statement.**  `qgScalaronFockHamiltonian` is the second-quantised gauge-fixed
`R + αR²` Hamiltonian with the scalaron sector on the whole nested Fock space
`⊕ₙ L²(ℝ^(n×2))`; `qgScalaronFock_esa` is its essential self-adjointness and
`qgScalaronFock_stone_flow` the resulting global unitary group `e^{−itH}`.

**4. The same in the mode (Hermite) realisation** used by the gravity chapters, where the
one-particle result is `BookProof.ScalaronEsa.qgScalaronMode_esa`: the nested Fock space
`⊕ₙ L²(ℕ)` of finite-particle occupancies carries `qgScalaronModeFockHamiltonian`, which is
symmetric (`qgScalaronModeFock_symmetric`), essentially self-adjoint
(`qgScalaronModeFock_esa`) and generates the unitary group
(`qgScalaronModeFock_stone_flow`).

## Honest boundary

The gluing is over an *orthogonal* direct sum of sectors: the Hamiltonian is assumed to
preserve particle number, which is exactly the finite-particle (nested Fock) situation
described in the plan.  Nothing here adds an interaction that changes the sector, and
nothing here uses a direct integral over a continuous parameter.  The kinetic term is not
part of these statements — as in `ChapterScalaronCoreEsa`, the potential is the object whose
exponential growth was in question, and the wave-operator combination remains where that
module left it.
-/

open Filter Topology MeasureTheory SchwartzMap

namespace BookProof.ScalaronFock

open BookProof.FarisLavine BookProof BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.QuantumGravityDensitized BookProof.ChapterStoneResolvent

noncomputable section

/-! ## 1. The nested Fock space over a family of configuration sectors -/

section Generic

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
  [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]

/-- The `n`-particle sector `L²(Eₙ)`. -/
abbrev sector (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)]
    [∀ n, InnerProductSpace ℝ (E n)] [∀ n, FiniteDimensional ℝ (E n)]
    [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)] (n : ℕ) :=
  Lp ℂ 2 (volume : Measure (E n))

/-- **The nested Fock space** `⊕ₙ L²(Eₙ)` of the finite-particle sectors. -/
abbrev nestedFock (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)]
    [∀ n, InnerProductSpace ℝ (E n)] [∀ n, FiniteDimensional ℝ (E n)]
    [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)] :=
  lp (fun n : ℕ => sector E n) 2

/-- **The Fock core**: the algebraic direct sum of the compactly supported smooth cores of
the sectors. -/
def nestedCore (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)]
    [∀ n, InnerProductSpace ℝ (E n)] [∀ n, FiniteDimensional ℝ (E n)]
    [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)] :
    Submodule ℂ (nestedFock E) :=
  dsCore (fun n => ccDomain (E n))



/-- **The second-quantised multiplication operator**: on the `n`-particle sector it is
multiplication by the `n`-particle potential `W n`. -/
def fockSmoothPotentialOp (W : ∀ n, E n → ℝ)
    (hW : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W n)) :
    nestedCore E →ₗ[ℂ] nestedFock E :=
  dsOp (fun n => opCc (W n) (hW n))









end Generic

/-! ## 2. The many-body gauge-fixed `R + αR²` potential -/

/-- The `n`-particle configuration sector: each of the `n` quanta carries a conformal mode
`R_c` (index `0`) and a scalaron field value `φ` (index `1`). -/
abbrev qgSector (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin 2)

/-- The direction reading off the `i`-th field of the `j`-th quantum. -/
def qgDir (n : ℕ) (j : Fin n) (i : Fin 2) : qgSector n :=
  EuclideanSpace.single (j, i) (1 : ℝ)



/-- **The many-body gauge-fixed `R + αR²` potential** on the `n`-particle sector: the sum
over the quanta of the one-particle potential `V₃(R_c) + V(φ)` of
`BookProof.ScalaronEsa.scalaronFullPotential`. -/
def qgManyPotential (M alpha : ℝ) (n : ℕ) (x : qgSector n) : ℝ :=
  ∑ j : Fin n, scalaronFullPotential M alpha (qgDir n j 0) (qgDir n j 1) x





theorem contDiff_qgManyPotential (M alpha : ℝ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (qgManyPotential M alpha n) :=
  ContDiff.sum (fun j _ => contDiff_scalaronFullPotential M alpha (qgDir n j 0) (qgDir n j 1))





/-! ## 3. The scalaron Hamiltonian on the nested Fock space -/

/-- **The nested Fock space of the scalaron sector**, `⊕ₙ L²(ℝ^(n×2))`. -/
abbrev qgFock := nestedFock qgSector

/-- The Fock core: the algebraic direct sum of the compactly supported smooth sector
cores. -/
abbrev qgFockCore : Submodule ℂ qgFock := nestedCore qgSector

/-- **The second-quantised gauge-fixed `R + αR²` Hamiltonian including the Starobinsky
scalaron potential**, on the nested Fock space: on the `n`-particle sector it is
multiplication by `∑ⱼ (V₃(R_c ⱼ) + V(φ ⱼ))`. -/
def qgScalaronFockHamiltonian (M alpha : ℝ) : qgFockCore →ₗ[ℂ] qgFock :=
  fockSmoothPotentialOp (fun n => qgManyPotential M alpha n)
    (fun n => contDiff_qgManyPotential M alpha n)











/-! ## 4. The same in the mode (Hermite) realisation -/

section Modes

variable (a b : ℕ → ℕ → ℝ) (M alpha : ℝ) (Rc phi : ℕ → ℕ → ℝ)

/-- The `n`-particle core of the mode realisation: the maximal domain of the `n`-particle
mode symbol. -/
def modeSectorCore (n : ℕ) : Submodule ℂ L2Nat :=
  mulSymbolDomain (qgModeSymbol (a n) (b n) (qgScalaronModePotential M alpha (Rc n) (phi n)))

/-- **The nested Fock space of the mode realisation**, `⊕ₙ L²(ℕ)`. -/
abbrev modeFock := lp (fun _ : ℕ => L2Nat) 2

/-- The Fock core of the mode realisation. -/
def modeFockCore : Submodule ℂ (modeFock) := dsCore (modeSectorCore a b M alpha Rc phi)

/-- **The second-quantised `R + αR²` mode Hamiltonian with the scalaron sector.** -/
def qgScalaronModeFockHamiltonian :
    modeFockCore a b M alpha Rc phi →ₗ[ℂ] modeFock :=
  dsOp (fun n => qgScalaronModeHamiltonian (a n) (b n) M alpha (Rc n) (phi n))













end Modes

end

end BookProof.ScalaronFock


