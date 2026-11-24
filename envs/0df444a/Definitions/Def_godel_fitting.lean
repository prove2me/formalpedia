-- Prove2me | Definitions.Def_godel_fitting
-- name    : godel_fitting
-- status  : Definition
-- author  : @LG
-- created : 2026-11-24T23:06:26.032768+00:00
-- url     : https://prove2.me/theorems/2317af66-b4f6-429a-b9e5-76ef99543ff6
-- title:
--   Fitting 2002: extensions and axioms
-- statement:
--   Fitting's extensional reading: extensions $I\to\mathrm{Prop}$, complement, entailment, God-likeness, essence, necessary existence, the four axiom records `AxCore`, `AxI`, `AxT3`, `Ax`, and the model data for the no-collapse and de-dicto countermodels.
-- source:
--   https://github.com/alozanoroble/godel-ontological-lean/blob/39066c5bbca03226873eccb8e60dab56b58e5c47/lean/Godel/Fitting.lean#L70-L160

import Definitions.Def_godel_modal

namespace Godel.Fitting

universe u v

abbrev Ext (I : Type v) : Type v := I → Prop

variable {W : Type u} {I : Type v}

def enot (S : Ext I) : Ext I := fun x => ¬ S x

def Entails (r : W → W → Prop) (Ex : I → W → Prop) (S T : Ext I) : Sentence W :=
  fun w => ∀ v, r w v → ∀ z, Ex z v → S z → T z

def God (P : Ext I → Sentence W) : I → Sentence W :=
  fun x w => ∀ S : Ext I, P S w → S x

def godExt (P : Ext I → Sentence W) (w : W) : Ext I := fun x => God P x w

def Ess (r : W → W → Prop) (Ex : I → W → Prop) (S : Ext I) (x : I) : Sentence W :=
  fun w => S x ∧ ∀ T : Ext I, T x → Entails r Ex S T w

def NE (r : W → W → Prop) (Ex : I → W → Prop) : I → Sentence W :=
  fun x w => ∀ S : Ext I, Ess r Ex S x w → ∀ v, r w v → ∃ z, Ex z v ∧ S z

def neExt (r : W → W → Prop) (Ex : I → W → Prop) (w : W) : Ext I :=
  fun x => NE r Ex x w

structure AxCore (r : W → W → Prop) (Ex : I → W → Prop)
    (P : Ext I → Sentence W) : Prop where
  A1a : ∀ (w : W) (S : Ext I), P (enot S) w → ¬ P S w
  A2  : ∀ (w : W) (S T : Ext I), P S w → Entails r Ex S T w → P T w
  /-- Fitting's own label (Proposition 11.16), **postulated** here rather than
  derived; it plays the role of Gödel's `A3` for the extensional reading. -/
  T2  : ∀ w : W, P (godExt P w) w

structure AxI (r : W → W → Prop) (Ex : I → W → Prop)
    (P : Ext I → Sentence W) : Prop extends AxCore r Ex P where
  A1b : ∀ (w : W) (S : Ext I), ¬ P S w → P (enot S) w

structure AxT3 (r : W → W → Prop) (Ex : I → W → Prop)
    (P : Ext I → Sentence W) : Prop extends AxCore r Ex P where
  A5 : ∀ w : W, P (neExt r Ex w) w

structure Ax (r : W → W → Prop) (Ex : I → W → Prop)
    (P : Ext I → Sentence W) : Prop extends AxI r Ex P where
  A4 : ∀ (w : W) (S : Ext I), P S w → ∀ v, r w v → P S v
  A5 : ∀ w : W, P (neExt r Ex w) w

variable {r : W → W → Prop} {Ex : I → W → Prop} {P : Ext I → Sentence W}

/-! ### From de re to de dicto

`A4` propagates positivity forward along `r`, which is enough to make
God-likeness itself stable, and with it to upgrade `T3` to the de dicto
reading. -/

/-! ### Modal collapse fails, even in `S5`

Two worlds, one individual existing at both, and a set is positive exactly
when the individual belongs to it.  All of Fitting's axioms hold and modal
collapse does not — over the universal relation, so this is an `S5` frame.

The contrast with `Godel.modal_collapse` is the whole point of the variant:
there, the sentence `p` entered as the constant intensional property
`λ y w. p w`; here the essence clause admits only extensions, and no extension
tracks `p`. -/

section NoCollapse

def cP : Ext Unit → Sentence Bool := fun S _ => S ()

def cEx : Unit → Bool → Prop := fun _ _ => True

end NoCollapse

/-! ### The two readings come apart on the Part I axioms

Two worlds and two individuals.  Each world sees only the *other* world, and
the individual existing at a world is the *other* one.  A set is positive at
`w` exactly when it contains `w`'s own individual — so the God-like individual
at each world is the one that does *not* exist there.

On `AxI` this is a model. God-like existence is de re possible
(`dd_possible_deRe`) and de dicto impossible (`dd_not_possible_deDicto`): at
the accessible world there is an existing individual God-like *as read off
here*, but the individual God-like *there* is not one that exists there.

`A4` necessarily fails (`dd_not_A4`) — it has to, since `T3_deDicto` is a
theorem once `A4` is available. -/

section DeDicto

def ddR : Bool → Bool → Prop := fun w v => w ≠ v

def ddEx : Bool → Bool → Prop := fun z v => z ≠ v

def ddP : Ext Bool → Sentence Bool := fun S w => S w

end DeDicto

end Godel.Fitting


