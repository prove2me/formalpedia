-- Prove2me | Definitions.Def_godel_scott
-- name    : godel_scott
-- status  : Definition
-- author  : @LG
-- created : 2026-11-24T22:57:03.262066+00:00
-- url     : https://prove2.me/theorems/9111e9c1-5423-4ef3-9412-fd7e981f97cd
-- title:
--   Scott 1987: definitions and axioms
-- statement:
--   Scott's variant: necessary existence $NE_S$ built on the repaired essence, the converse half $A1b$, Scott's $A5$, the positive-existence core `ScottCore`, and the full record `Scott1987`.
-- source:
--   https://github.com/alozanoroble/godel-ontological-lean/blob/39066c5bbca03226873eccb8e60dab56b58e5c47/lean/Godel/Scott.lean#L60-L110

import Definitions.Def_godel_original

namespace Godel

universe u v

variable {W : Type u} {I : Type v}
variable {r : W → W → Prop} {P : Property I W → Sentence W}

def NES (r : W → W → Prop) : Property I W :=
  fun x w => ∀ φ : Property I W, ScottEss r φ x w → box r (fun v => ∃ y, φ y v) w

abbrev AxiomA1b (P : Property I W → Sentence W) : Prop :=
  ∀ (w : W) (φ : Property I W), ¬ P φ w → P (pneg φ) w

abbrev AxiomA5S (r : W → W → Prop) (P : Property I W → Sentence W) : Prop :=
  ∀ w : W, P (NES r) w

structure ScottCore (r : W → W → Prop) (P : Property I W → Sentence W) : Prop where
  A1a : AxiomA1 P
  A2  : AxiomA2 r P
  A3  : AxiomA3 P

structure Scott1987 (r : W → W → Prop) (P : Property I W → Sentence W) : Prop
    extends ScottCore r P where
  A1b : AxiomA1b P
  A4  : AxiomA4 r P
  A5  : AxiomA5S r P

/-! ### A shorter route, and a warning about it

Everything above follows Scott's own argument.  The encoded system also admits
a much shorter route to the same conclusions, which uses neither `A1b` nor
`A4`.  It is recorded here because it is a genuine theorem of the encoding and
because the gap between it and Scott's argument is itself informative — but
read the caveat on `hae_scottEss` before drawing conclusions about Scott's
system as he intended it. -/

/-! ### What modal collapse does to the frame

Modal collapse is usually stated as a fact about sentences: every truth is
necessary.  Read semantically it is a fact about the *accessibility relation*,
and a drastic one.  Applying collapse to the sentence "being the world `w`"
shows that `w` sees nothing but itself; Theorem 1 applied to `A3` shows it does
see itself.  So `r` is forced to be equality, and every world is an isolated
point.

This is the standard semantic reading of modal collapse — Benzmüller and
others state `MC` directly as `∀x ∀y (r x y → y = x)` — not something new.
What it settles is a question about *models*: Scott's axioms are consistent
with `W` of any size, but never with a frame that has any modal structure. -/

end Godel


