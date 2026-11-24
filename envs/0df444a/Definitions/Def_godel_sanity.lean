-- Prove2me | Definitions.Def_godel_sanity
-- name    : godel_sanity
-- status  : Definition
-- author  : @LG
-- created : 2026-11-24T23:15:30.559227+00:00
-- url     : https://prove2.me/theorems/2ad21366-8645-46e9-8734-71ca5e780e87
-- title:
--   Models and countermodels: data
-- statement:
--   The one-world toy positivity, the isolated-worlds frame and positivity, and the no-symmetry frame and positivity used to separate the systems.
-- source:
--   https://github.com/alozanoroble/godel-ontological-lean/blob/39066c5bbca03226873eccb8e60dab56b58e5c47/lean/Godel/Sanity.lean#L30-L200

import Definitions.Def_godel_scott

namespace Godel

universe u

def toyP : Property Unit Unit → Sentence Unit := fun φ _ => φ () ()

/-! ### Gödel's A5 fails here -/
/-! ### Scott's A5 holds here -/
/-! ## Models with as many worlds as you like

`Godel.accessibility_eq` says Scott's axioms force `r` to be equality.  That
leaves an obvious question: is such a frame satisfiable with more than one
world, or does something else collapse the world set too?

It is satisfiable, for `W` of any size whatsoever.  Take equality as the
accessibility relation and one individual, and let a property be positive at a
world exactly when that individual has it there.  Each world is then an
isolated copy of the toy model, with its own God-like individual, seeing
nothing but itself.

So the answer to "does Scott's system have a non-degenerate model?" is: yes in
cardinality, no in modal structure.  `W` may be a proper class of worlds; none
of them can see another, so `□` and `◇` are inert (`box_iff`, `dia_iff`) and
nothing modal is being said.  The one-world model above is not forced — but
nothing better than a disjoint heap of one-world models is available either. -/

section Isolated

variable (V : Type u)

def isoR : V → V → Prop := fun w v => v = w

def isoP : Property Unit V → Sentence V := fun φ w => φ () w

end Isolated

/-! ## Symmetry cannot be traded for `S4`

`exists_god` is the only place the positive argument uses a frame condition,
and it uses symmetry: it needs to carry `□∃x G(x)`, established at some
*possible* world, back to the actual one.  That is the `B` schema
`◇□p → p`.  Could the other two `S5` conditions do the job instead?

No.  The model below is **reflexive and transitive** — an `S4` frame —
satisfies all of Scott's axioms, and refutes Theorem 3, modal collapse and
`accessibility_eq` outright.

**Be careful what this shows.**  It shows the symmetry hypothesis cannot be
deleted from the `KB` results in favour of reflexivity and transitivity.  It
does **not** show that symmetry is necessary in the absolute sense: some frame
condition weaker than, or incomparable with, symmetry might still suffice, and
no correspondence or minimality theorem here excludes that.  An earlier
version of this file said "symmetry is really needed", which claimed more than
the countermodel delivers.

Two worlds, `false` and `true`.  `false` sees both; `true` sees only itself.
One individual.  A property is positive, at either world, exactly when the
individual has it **at `true`**.  So `true` is a world where the toy model of
`toy_satisfies_scott` lives, and `false` is a world that can see it but is not
seen by it.  All the positivity facts are imported from `true`, which is what
keeps the axioms true at `false`; but God-likeness is not, because being
God-like at `false` would require having there every property one has at
`true`, and "being the world `true`" is such a property.

The moral: Scott's axioms do not entail modal collapse on their own.  They
entail it *in `B` and `S5`*, which is where the argument is always presented.
-/

section NoSymmetry

def nsR : Bool → Bool → Prop := fun w v => w = true → v = true

def nsP : Property Unit Bool → Sentence Bool := fun φ _ => φ () true

end NoSymmetry

end Godel


