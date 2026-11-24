-- Prove2me | Definitions.Def_godel_anderson
-- name    : godel_anderson
-- status  : Definition
-- author  : @LG
-- created : 2026-11-24T23:01:47.492985+00:00
-- url     : https://prove2.me/theorems/64369eb7-ee3d-4564-b93a-144b9ba3903f
-- title:
--   Anderson 1990: definitions and axioms
-- statement:
--   Anderson's emendation: biconditional God-likeness $G^A$, biconditional essence, necessary existence, the core record `AxCore` ($A1^*,A2,A3^*$) and the full `Ax`, plus the two-world no-collapse positivity `cP`.
-- source:
--   https://github.com/alozanoroble/godel-ontological-lean/blob/39066c5bbca03226873eccb8e60dab56b58e5c47/lean/Godel/Anderson.lean#L70-L140

import Definitions.Def_godel_original

namespace Godel.Anderson

open Godel

universe u v

variable {W : Type u} {I : Type v}

def God (r : W → W → Prop) (P : Property I W → Sentence W) : Property I W :=
  fun x w => ∀ φ : Property I W, P φ w ↔ box r (φ x) w

def Ess (r : W → W → Prop) (φ : Property I W) (x : I) : Sentence W :=
  fun w => ∀ ψ : Property I W,
    box r (ψ x) w ↔ box r (fun v => ∀ y, φ y v → ψ y v) w

def NE (r : W → W → Prop) : Property I W :=
  fun x w => ∀ φ : Property I W, Ess r φ x w → box r (fun v => ∃ y, φ y v) w

structure AxCore (r : W → W → Prop) (P : Property I W → Sentence W) : Prop where
  /-- **A1\*.**  Anderson's retained half of Gödel's `A1`; `A1b` is dropped. -/
  A1a : AxiomA1 P
  /-- **A2.**  Positivity is closed under necessary entailment. -/
  A2 : AxiomA2 r P
  /-- **A3\*.**  The revised God-likeness is positive. -/
  A3p : ∀ w : W, P (God r P) w

structure Ax (r : W → W → Prop) (P : Property I W → Sentence W) : Prop
    extends AxCore r P where
  /-- **A4.**  Positive properties are necessarily positive. -/
  A4 : ∀ (w : W) (φ : Property I W), P φ w → box r (P φ) w
  /-- **A5\*.**  Necessary existence is positive. -/
  A5 : ∀ w : W, P (NE r) w

variable {r : W → W → Prop} {P : Property I W → Sentence W}

/-! ### The direct route to `T3`

Three short lemmas, no frame condition until the last step, and `A4`/`A5`
nowhere. -/

/-! ### `A4` and `A5` are redundant

Benzmüller, Weber and Woltzenlogel Paleo (2017) report both as redundant for
Anderson's emendation under the constant-domain reading — `A5` already in `K`,
`A4` in `K4B`.  Both are proved here. -/

/-! ### Anderson's own route, for comparison

The essence argument reconstructed.  It reaches the same `T3` but consumes
reflexivity and transitivity on top of symmetry, and uses `A4` and `A5`.  Kept
because the contrast is the point: the cost is in the route, not in Anderson's
system. -/

/-! ### Modal collapse fails, even in `S5`

Two worlds, one individual, and a property is positive exactly when the
individual has it at *every* world.  All of Anderson's axioms hold over the
universal relation, and modal collapse does not.

The mechanism: `Gᴬ` and `essᴬ` are stated entirely in terms of `□`, so a
merely contingent sentence never satisfies the antecedent of the essence
clause, and the collapse derivation of `Godel.modal_collapse` has no
counterpart. -/

section NoCollapse

def cP : Property Unit Bool → Sentence Bool := fun φ _ => ∀ v, φ () v

end NoCollapse

end Godel.Anderson


