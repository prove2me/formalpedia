-- Prove2me | Definitions.Def_ChapterVielbeinFiberFock
-- name    : ChapterVielbeinFiberFock
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T15:10:00.246622+00:00
-- url     : https://prove2.me/theorems/2ef89f96-0758-48d5-b10d-0f14e6d02783
-- title:
--   The Lean 4 theorem `contDiff_shearEnergy` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterVielbeinFiberFock.lean`): generated def bundle for ChapterVielbeinFiberFock. See BookProof/ChapterVielbeinFiberFock.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterVielbeinFiberFock.lean

import Theorems.Thm_BookProof_ScalaronEsa_contDiff_scalaronAlong

import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterScalaronEdge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Mathlib


/-!
# The vielbein/TEGR fibrewise reassembly: shear fibers plus the scalaron fiber

`CONSOLIDATED_PLAN.md`, next-steps item **4(a)** of the 2026-08-28j block: *the explicit
fibrewise reassembly instance naming the TEGR shear fibers plus the scalaron fiber*, as thin
glue over the generic instrument `BookProof.ScalaronFock.fockSmoothPotential_esa`.

The vielbein (TEGR) gauge fixing of `docs/qg_starobinsky_vielbein_hamiltonian.cdb` gives each
quantum `d` shear field values `y₁, …, y_d` — per-mode harmonic fibers with constant positive
frequencies `ω₁, …, ω_d` — together with one scalaron field value `φ`, whose potential is
*exactly* the formalized Einstein-frame potential `starobinskyV`
(`BookProof.Starobinsky.starobinskyV`).  This module writes that fiber list down as an
explicit family of `n`-particle configuration sectors with an explicit `n`-particle
potential, and runs the generic direct-sum machinery on it.

## What is proved

* `vielbeinManyPotential` — the `n`-particle potential
  `∑ⱼ (∑ᵢ ½ωᵢ² yᵢ(j)² + V(φ(j)))` on the sector `ℝ^(n × (d+1))`, with
  `vielbeinManyPotential_apply` reading it off in coordinates and
  `vielbeinManyPotential_scalaron_fiber` identifying the last fiber of each quantum as the
  formalized scalaron potential.
* `contDiff_vielbeinManyPotential`, `vielbeinManyPotential_nonneg` — smoothness, and
  non-negativity for `0 < α` (the shear fibers are squares, the scalaron potential is a
  square: `starobinskyV_nonneg`).
* `vielbeinFock_symmetric`, `vielbeinFock_deficiencyTrivialAt`, **`vielbeinFock_esa`**,
  `vielbeinFock_stone_flow` — the reassembled operator on the nested Fock space
  `⊕ₙ L²(ℝ^(n × (d+1)))` is densely defined, symmetric, has trivial deficiency off the real
  axis, is essentially self-adjoint, and generates a complete unitary group.
* `vielbeinFock_potential_ge` — the uniform fibrewise lower bound `0` of the reassembled
  potential.

## Honest boundary

* What is unconditional: the reassembly itself — that the family "`d` harmonic shear fibers
  plus one Starobinsky scalaron fiber per quantum" produces an essentially self-adjoint
  multiplication operator on the nested Fock space, with a uniform lower bound.
* What stays a modelling statement: that this fiber list *is* the vielbein/TEGR gauge-fixed
  Hamiltonian's field content, and the values of the shear frequencies `ω`.  As elsewhere in
  the project, the TEGR kinetic/gravity sector is untouched; no mass gap of a physical
  Yang–Mills or gravity Hamiltonian is claimed here.
* This module is the *potential* half of the fiber reassembly, matching the generic
  instrument it glues (`fockSmoothPotentialOp` is multiplication by the `n`-particle
  potential).  The strict one-particle edge of the scalaron fiber, kinetic term included,
  is the separate theorem `BookProof.ScalaronEdge.starobinskyEdge_quadForm`.
-/

open Filter Topology MeasureTheory

namespace BookProof.VielbeinFock

open BookProof.Starobinsky BookProof.ScalaronEsa BookProof.ScalaronFock
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.FarisLavine BookProof.ChapterStoneResolvent

noncomputable section

/-! ## 1. The fiber list: `d` shear fibers and one scalaron fiber per quantum -/

/-- The `n`-particle configuration sector of the vielbein model: each of the `n` quanta
carries `d` TEGR shear field values (indices `0, …, d−1`) and one scalaron field value
(index `Fin.last d`). -/
abbrev vielbeinSector (d n : ℕ) := EuclideanSpace ℝ (Fin n × Fin (d + 1))

/-- The direction reading off the `i`-th field of the `j`-th quantum. -/
def vielbeinDir (d n : ℕ) (j : Fin n) (i : Fin (d + 1)) : vielbeinSector d n :=
  EuclideanSpace.single (j, i) (1 : ℝ)



/-- The shear energy of a single quantum: the `d` harmonic TEGR shear fibers with the
per-mode frequencies `ω`. -/
def shearEnergy (d : ℕ) (om : Fin d → ℝ) (n : ℕ) (j : Fin n) (x : vielbeinSector d n) : ℝ :=
  ∑ i : Fin d, om i ^ 2 / 2 * (inner ℝ x (vielbeinDir d n j i.castSucc) : ℝ) ^ 2

/-- **The many-body vielbein/TEGR potential**: for each quantum, the harmonic shear fibers
plus the Einstein-frame Starobinsky potential of its scalaron fiber. -/
def vielbeinManyPotential (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) (n : ℕ)
    (x : vielbeinSector d n) : ℝ :=
  ∑ j : Fin n, (shearEnergy d om n j x
    + starobinskyV M alpha (inner ℝ x (vielbeinDir d n j (Fin.last d))))







theorem contDiff_shearEnergy (d : ℕ) (om : Fin d → ℝ) (n : ℕ) (j : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (shearEnergy d om n j) := by
  refine ContDiff.sum (fun i _ => ?_)
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : vielbeinSector d n => (inner ℝ x (vielbeinDir d n j i.castSucc) : ℝ)) :=
    ((innerSL ℝ).flip (vielbeinDir d n j i.castSucc)).contDiff
  exact contDiff_const.mul (h.pow 2)

theorem contDiff_vielbeinManyPotential (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (vielbeinManyPotential M alpha d om n) :=
  ContDiff.sum (fun j _ =>
    (contDiff_shearEnergy d om n j).add (contDiff_scalaronAlong M alpha _))







/-! ## 2. The reassembly on the nested Fock space -/

/-- **The nested Fock space of the vielbein model**, `⊕ₙ L²(ℝ^(n × (d+1)))`. -/
abbrev vielbeinFock (d : ℕ) := nestedFock (vielbeinSector d)

/-- The Fock core: the algebraic direct sum of the compactly supported smooth sector
cores. -/
abbrev vielbeinFockCore (d : ℕ) : Submodule ℂ (vielbeinFock d) := nestedCore (vielbeinSector d)

/-- **The second-quantised vielbein/TEGR potential** on the nested Fock space: on the
`n`-particle sector it is multiplication by `∑ⱼ (∑ᵢ ½ωᵢ² yᵢ(j)² + V(φ(j)))`. -/
def vielbeinFockHamiltonian (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) :
    vielbeinFockCore d →ₗ[ℂ] vielbeinFock d :=
  fockSmoothPotentialOp (fun n => vielbeinManyPotential M alpha d om n)
    (fun n => contDiff_vielbeinManyPotential M alpha d om n)













end

end BookProof.VielbeinFock


