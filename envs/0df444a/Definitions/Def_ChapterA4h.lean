-- Prove2me | Definitions.Def_ChapterA4h
-- name    : ChapterA4h
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T07:35:30.677064+00:00
-- url     : https://prove2.me/theorems/9dbbb849-507f-4a05-a49b-3c5657983326
-- title:
--   Chapter A4h
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA4h.lean`): generated def bundle for ChapterA4h. See BookProof/ChapterA4h.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA4h.lean

import Definitions.Def_ChapterA4e
import Definitions.Def_ChapterA4f
import Definitions.Def_ChapterA5
import Mathlib


/-!
# Chapter A4h — the Wigner/Mackey exhaustiveness bundle (roadmap N11, §A.4–A.5)

This file assembles the *exhaustiveness clauses* of Props 87/88 and Cor 1 of the
book's §A.4/A.5.  Following the design of `IsSchurFull` / `PauliFundamental`
(§A.2/§A.3), the genuinely external inputs — Wigner's 1939 little-group
classification and Mackey's imprimitivity theorem — are introduced as **named
hypotheses with citation docstrings, never as `axiom`s**; the *conditional
headline theorems* are then proved around them, reusing the on-disk exclusion
cores of `ChapterA4e`/`ChapterA4f`/`ChapterA5`.

## Concrete payload (fully proved, no external input)

* `localizable_iff_massShell` — the concrete Majorana energy symbol
  `energySymbolR p m₁ m₂` (§A.5) is singular **iff** we sit on the mass shell
  `|p⃗|² = m₁² + m₂²`.  (From `ChapterA5.energySymbolR_sq`.)
* `not_localizable_of_tachyon`, `not_localizable_zeroMomentum` — the tachyonic
  (`m² > |p⃗|²`) and zero-momentum (`p = 0`, `m ≠ 0`) symbols are everywhere
  invertible, hence not localizable.  (Exclusions 1–2 of Prop 87.)

## External bundle (named hypotheses, cited, never axioms)

* `MackeyImprimitivity` (Mackey 1949/1952; Varadarajan Thm 6.12): a localizable
  unitary irrep is induced, hence realized by a concrete localizable energy
  symbol.
* `WignerClassification` (Wigner 1939): the massless *continuous-spin* class does
  not occur among localizable induced irreps (cf. `ChapterA4f.infinite_spin_excluded`).

## Conditional headlines

* `prop87_assembled` — a localizable induced irrep is **massive** or
  **massless with discrete helicity** (tachyons excluded by the concrete mass
  shell, infinite spin excluded by Wigner).
* `prop88_energy_sign_not_conserved` + `cor1_energy_sectors_swapped` — the
  energy-sign projectors are not conserved and are exchanged by spatial motion:
  antiparticles / CPT (from `ChapterA4e`).
* `prop87_88_assembled` — the combined Prop 87 + Prop 88 statement.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); the `EXTERNAL` inputs are hypotheses, not axioms.
-/

open Matrix

namespace BookProof.ChapterA4h

open BookProof.ChapterA4e BookProof.ChapterA4f BookProof.ChapterA5

/-! ## Concrete localizability of the Majorana energy symbol -/

/-- A relativistic wave operator is *localizable* on its orbit when its energy
symbol is singular (admits a nontrivial kernel — the mass shell on which the
localized state sits).  An everywhere-invertible symbol carries no proper
invariant subspace, which is the mathematical form of the Prop 87 exclusions. -/
def Localizable (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) : Prop :=
  ¬ IsUnit (energySymbolR p m₁ m₂).det







/-! ## The five Wigner kinematic types -/

/-- The five kinematic types of a relativistic unitary irrep, per Wigner's 1939
classification by the sign of the mass Casimir `P²` and the little group. -/
inductive PoincareType
  | massive
  | masslessDiscrete
  | tachyon
  | zeroMomentum
  | infiniteSpin
  deriving DecidableEq, Repr

/-- The kinematic type read off from the mass-squared Casimir and the
massless continuous-spin flag. -/
noncomputable def PoincareType.of (massSq : ℝ) (contSpin : Bool) : PoincareType :=
  if 0 < massSq then .massive
  else if massSq = 0 then (if contSpin then .infiniteSpin else .masslessDiscrete)
  else .tachyon

/-! ## External bundle (named hypotheses; cite, never axiomatize) -/

variable (R : Type*)

/-- **Mackey imprimitivity** (Mackey 1949/1952; Varadarajan, *Geometry of
Quantum Theory*, Thm 6.12), taken as an `EXTERNAL` named hypothesis (not in
Mathlib).  Every localizable unitary irreducible representation of the Poincaré
group is induced from a little-group representation, hence realized by the
concrete Majorana energy symbol of §A.5 on a definite orbit `(p, m₁, m₂)`, with
the symbol singular on its mass shell (localizable). -/
structure MackeyImprimitivity where
  /-- The orbit 3-momentum of the induced realization. -/
  mom : R → (Fin 3 → ℝ)
  /-- The two Majorana mass parameters of the induced realization. -/
  mass₁ : R → ℝ
  mass₂ : R → ℝ
  /-- The massless continuous-spin flag (nontrivial `SE(2)` translations). -/
  contSpin : R → Bool
  /-- The induced realization is localizable (sits on its mass shell). -/
  induced : ∀ ρ, Localizable (mom ρ) (mass₁ ρ) (mass₂ ρ)

/-- The mass-squared Casimir of a Mackey-induced irrep. -/
def MackeyImprimitivity.massSq {R : Type*} (Mk : MackeyImprimitivity R) (ρ : R) : ℝ :=
  Mk.mass₁ ρ ^ 2 + Mk.mass₂ ρ ^ 2

/-- **Wigner classification** (Wigner, *Ann. Math.* 40 (1939) 149), taken as an
`EXTERNAL` named hypothesis.  Among the localizable induced irreps, the massless
*continuous-spin* ("infinite spin") class does not occur: the `SE(2)` translation
label cannot be discretized (the concrete obstruction is
`ChapterA4f.infinite_spin_excluded`). -/
structure WignerClassification (Mk : MackeyImprimitivity R) : Prop where
  /-- No localizable massless irrep has continuous spin. -/
  no_continuous_spin : ∀ ρ, Mk.massSq ρ = 0 → Mk.contSpin ρ = false

/-! ## Conditional headlines -/









end BookProof.ChapterA4h


