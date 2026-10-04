-- Prove2me | Definitions.Def_ChapterA4g
-- name    : ChapterA4g
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T07:51:53.349996+00:00
-- url     : https://prove2.me/theorems/66443a65-84e1-4d75-8204-d9d8f60220fd
-- title:
--   Chapter A4g
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA4g.lean`): generated def bundle for ChapterA4g. See BookProof/ChapterA4g.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA4g.lean

import Definitions.Def_ChapterA4c
import Definitions.Def_ChapterA4d
import Definitions.Def_ChapterA4e
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib


/-!
# Chapter A, §A.4 — Prop 81 / Notes 80–83: the Bargmann–Wigner rep group laws

Source: `book.tex` §A.4 (line 5636), **Notes 80–83 / Proposition 81** — the
massive (Note 80 complex / **Prop 81** real) and massless-discrete-helicity
(Notes 82–83) irreducible projective Poincaré representations, realized in the
Majorana formalism with the explicit little-group action `L_S` and translation
action `T_a`.

Following the roadmap directive for this item ("state the reps as structures and
*verify the group-rep axioms* for the given `L_S, T_a` (checkable), citing Wigner
for exhaustiveness"), this file formalizes the concrete, self-contained
**group-representation axioms** of the little-group and translation factors of
the Poincaré rep, on the `2×2` little-group models of §A.4:

* **Massive little group `SU(2)` (Prop 79, `ChapterA4c`).** The spin-`½` factor
  `L_S` is the defining representation `S ↦ S` of the massive little group. Its
  representation axioms are the group axioms of `SUtwo`:
  `SUtwo_one_mem` (identity), `SUtwo_mul_mem` (closure — respects composition),
  `SUtwo_conjTranspose_mem` / `SUtwo_inv` (`S⁻¹ = S†` is again in `SU(2)`). The
  higher spin-`j` reps are the symmetric tensor powers of this defining rep
  (`EXTERNAL` Wigner exhaustiveness; the base case is here).
* **Massless little group `SE(2)` (Prop 79, `ChapterA4d`).** The
  discrete-helicity factor is realized on `SEtwo`; the same group axioms
  `SEtwo_one_mem`, `SEtwo_mul_mem` verify it is a representation domain.
* **Translation factor `T_a`.** On 3-momentum space the translation by `a⃗` acts
  as the phase `T_a(p⃗) = e^{i p⃗·a⃗}`. Its representation axioms are additivity
  `transPhase_add` (`T_{a+b} = T_a T_b`), `transPhase_zero` (`T_0 = 1`), and
  unitarity `transPhase_abs` (`|T_a| = 1`) — the abelian translation subgroup is
  represented by unit-modulus phases (a genuine unitary one-parameter-per-axis
  group).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); **no `EXTERNAL` hypothesis** enters these group-law verifications
(the *exhaustiveness* of the Bargmann–Wigner classification — that these are
*all* the irreps — is the cited Wigner 1939 / Mackey backbone, not these
axiom checks).
-/

open Matrix
open scoped ComplexConjugate

namespace BookProof.ChapterA4g

open BookProof.ChapterA3

/-! ## The massive little group `SU(2)` — spin-½ defining-rep axioms -/









/-! ## The massless little group `SE(2)` — discrete-helicity-rep axioms -/





/-! ## The translation factor `T_a(p⃗) = e^{i p⃗·a⃗}` -/

/-- The momentum-space translation phase `T_a(p⃗) = exp(i p⃗·a⃗)`. -/
noncomputable def transPhase (p a : Fin 3 → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((∑ j, p j * a j : ℝ) : ℂ))







/-! ## Constraint preservation: the massive little group fixes the rest frame

On the `4×4` Majorana model the spatial rotation generators `γⁱγʲ` (the Lie
algebra of the massive little group `SU(2)`, which fixes the standard rest
momentum) commute with the energy-sign operator `iγ⁰` of `ChapterA4e`, hence with
the positive-energy Dirac projector `P₊`.  This is the Bargmann–Wigner
rep-consistency statement for the massive irreps: the massive little-group action
preserves the positive-energy (Dirac) constraint subspace. -/

open BookProof.ChapterA5 (spatialIdx coeffMass1Z)
open BookProof.ChapterA4e (enSign projPos)

/-- The spatial rotation generator `γⁱγʲ` (a generator of the massive little
group `SU(2)`), over `ℤ`. -/
def rotGenZ (i j : Fin 3) : Matrix (Fin 4) (Fin 4) ℤ :=
  mgammaZ (spatialIdx i) * mgammaZ (spatialIdx j)



/-- The spatial rotation generator `γⁱγʲ` as a complex matrix. -/
noncomputable def rotGen (i j : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  (Int.castRingHom ℂ).mapMatrix (rotGenZ i j)





end BookProof.ChapterA4g


