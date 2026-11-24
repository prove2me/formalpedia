-- Prove2me | Definitions.Def_godel_original
-- name    : godel_original
-- status  : Definition
-- author  : @LG
-- created : 2026-11-24T22:42:26.103133+00:00
-- url     : https://prove2.me/theorems/36833c36-e792-475d-9975-60d1fc18e2c0
-- title:
--   Gödel 1970: definitions and axioms
-- statement:
--   Gödel's 1970 primitives: God-likeness $G$, his essence $\mathrm{ess}$ (without the conjunct $\varphi(x)$), Scott's repaired essence, necessary existence $NE$, the five axioms $A1$–$A5$ as world-indexed hypotheses, the bundled record `Godel1970`, and the empty property.
-- source:
--   https://github.com/alozanoroble/godel-ontological-lean/blob/39066c5bbca03226873eccb8e60dab56b58e5c47/lean/Godel/Original.lean#L62-L130

import Definitions.Def_godel_modal

namespace Godel

universe u v

variable {W : Type u} {I : Type v}
variable {r : W → W → Prop} {P : Property I W → Sentence W}

def God (P : Property I W → Sentence W) : Property I W :=
  fun x w => ∀ φ : Property I W, P φ w → φ x w

def Ess (r : W → W → Prop) (φ : Property I W) (x : I) : Sentence W :=
  fun w => ∀ ψ : Property I W, ψ x w → box r (fun v => ∀ y, φ y v → ψ y v) w

def ScottEss (r : W → W → Prop) (φ : Property I W) (x : I) : Sentence W :=
  fun w => φ x w ∧ ∀ ψ : Property I W, ψ x w → box r (fun v => ∀ y, φ y v → ψ y v) w

def NE (r : W → W → Prop) : Property I W :=
  fun x w => ∀ φ : Property I W, Ess r φ x w → box r (fun v => ∃ y, φ y v) w

/-! ### The axioms, stated individually

Each is asserted to hold at *every* world.  They are named so that the
hypotheses of each theorem below say exactly which of Gödel's axioms it
consumes. -/

abbrev AxiomA1 (P : Property I W → Sentence W) : Prop :=
  ∀ (w : W) (φ : Property I W), P (pneg φ) w → ¬ P φ w

abbrev AxiomA2 (r : W → W → Prop) (P : Property I W → Sentence W) : Prop :=
  ∀ (w : W) (φ ψ : Property I W),
    P φ w → box r (fun v => ∀ x, φ x v → ψ x v) w → P ψ w

abbrev AxiomA3 (P : Property I W → Sentence W) : Prop :=
  ∀ w : W, P (God P) w

abbrev AxiomA4 (r : W → W → Prop) (P : Property I W → Sentence W) : Prop :=
  ∀ (w : W) (φ : Property I W), P φ w → box r (P φ) w

abbrev AxiomA5 (r : W → W → Prop) (P : Property I W → Sentence W) : Prop :=
  ∀ w : W, P (NE r) w

structure Godel1970 (r : W → W → Prop) (P : Property I W → Sentence W) : Prop where
  A1 : AxiomA1 P
  A2 : AxiomA2 r P
  A3 : AxiomA3 P
  A4 : AxiomA4 r P
  A5 : AxiomA5 r P

def emptyProperty (I : Type v) (W : Type u) : Property I W := fun _ _ => False

end Godel


