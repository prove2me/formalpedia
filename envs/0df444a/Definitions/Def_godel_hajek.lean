-- Prove2me | Definitions.Def_godel_hajek
-- name    : godel_hajek
-- status  : Definition
-- author  : @LG
-- created : 2026-11-24T23:11:33.610097+00:00
-- url     : https://prove2.me/theorems/128cd295-9d90-4d02-9f78-848389618ca8
-- title:
--   Hájek 2002 (AOE): definitions and axioms
-- statement:
--   Hájek's emendation: $P^\#$ (necessarily implied by a positive property), biconditional God-likeness $G^H$, the merged axiom $H{:}A12$ with $A3$ in `AxCore`, the full `Ax`, and the no-collapse positivity `hP`.
-- source:
--   https://github.com/alozanoroble/godel-ontological-lean/blob/39066c5bbca03226873eccb8e60dab56b58e5c47/lean/Godel/Hajek.lean#L60-L120

import Definitions.Def_godel_anderson

namespace Godel.Hajek

open Godel

universe u v

variable {W : Type u} {I : Type v}

def Pstar (r : W → W → Prop) (P : Property I W → Sentence W)
    (φ : Property I W) : Sentence W :=
  fun w => ∃ ψ : Property I W, P ψ w ∧ box r (fun v => ∀ y, ψ y v → φ y v) w

def God (r : W → W → Prop) (P : Property I W → Sentence W) : Property I W :=
  fun x w => ∀ φ : Property I W, box r (φ x) w ↔ Pstar r P φ w

structure AxCore (r : W → W → Prop) (P : Property I W → Sentence W) : Prop where
  /-- **H:A12.**  Merges Anderson's `A1a` and `A2` into one weaker axiom. -/
  A12 : ∀ (w : W) (φ ψ : Property I W),
    P φ w → box r (fun v => ∀ x, φ x v → ψ x v) w → ¬ P (pneg ψ) w
  /-- **A3** (written `A3′` in the literature, to distinguish it from
  Gödel's `A3`, since it is stated for Hájek's own `Gᴴ`).  Being God-like is
  positive. -/
  A3 : ∀ w : W, P (God r P) w

structure Ax (r : W → W → Prop) (P : Property I W → Sentence W) : Prop
    extends AxCore r P where
  /-- **A4.**  Positive properties are necessarily positive. -/
  A4 : ∀ (w : W) (φ : Property I W), P φ w → box r (P φ) w
  /-- **A5.**  Necessary existence — Anderson's — is positive. -/
  A5 : ∀ w : W, P (Anderson.NE r) w

variable {r : W → W → Prop} {P : Property I W → Sentence W}

/-! ### Modal collapse fails, even in `S5`

Two worlds, one individual; a property is positive exactly when the individual
has it at *every* world.  All of `AOE` holds — including `A4` and `A5`, so this
also certifies the consistency of the full axiom set — and modal collapse does
not.

As with Anderson's variant, the reason is that `Gᴴ` is stated entirely in terms
of `□`: a merely contingent sentence never reaches the biconditional. -/

section NoCollapse

def hP : Property Unit Bool → Sentence Bool := fun φ _ => ∀ v, φ () v

end NoCollapse

end Godel.Hajek


