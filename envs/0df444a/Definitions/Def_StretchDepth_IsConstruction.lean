-- Prove2me | Definitions.Def_StretchDepth_IsConstruction
-- name    : StretchDepth_IsConstruction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:04:02.480193+00:00
-- url     : https://prove2.me/theorems/3be867f8-cb4c-49c3-aaff-f7e2c1ea02c2
-- title:
--   $(q,d)$-constructions and the no-repeat form
-- statement:
--   A **$(q,d)$-construction** $H^{(\cdot)}:\{0,1\}^m\to\{0,1\}^M$ from an inner function $G:\{0,1\}^n\to\{0,1\}^N$ assigns a round tree to each input $x$, such that for every oracle $G$ the run on $x$ makes at most $q$ queries in at most $d$ rounds. The number $d$ is the **adaptivity depth**.
--
--   The construction has **no repeated queries** if for every oracle $G$ and every $x$ no input is queried twice during the run.
--
--   These are the objects of the depth lower bounds: a composition of a length-doubling generator $d$ times is a $(q,d)$-construction.
--
--   **Formalization Note** The bounds quantify over real oracles, so a branch that no oracle reaches is unconstrained. The no-repeat condition is a separate predicate, because the page's bounds count with multiplicity; passing to it is a milestone.
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), Definition 1, p.13

import Definitions.Def_StretchDepth_RoundTree

namespace StretchDepth

variable {n N m M : ℕ}

/-- **`(q, d)`-construction.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), Definition 1, p.13: "on every input x ∈ {0, 1}m and for every oracle G, outputs
a value HG(x) ∈ {0, 1}M which is determined by making at most q queries to G in at most d adaptive
rounds."

`H` assigns a round tree to each input, and on every input and every oracle the run makes at most
`q` queries (with multiplicity) in at most `d` rounds.

**Formalization Note.** The bounds quantify over real oracles only, as the page does: a branch of
the tree that no oracle reaches is unconstrained. An empty batch counts as a round; it can be
deleted, so this does not change the class up to removing such rounds. -/
def IsConstruction (H : Bits m → RoundTree n N M) (q d : ℕ) : Prop :=
  ∀ (G : Bits n → Bits N) (x : Bits m), numQueries G (H x) ≤ q ∧ numRounds G (H x) ≤ d

/-- Definition 1, last sentence, p.13: "no input is queried more than once in an execution of
HG(x)." Not part of `IsConstruction`: the page's bounds count with multiplicity, and passing to
this form is the milestone `no_repeat_normal_form`. -/
def NoRepeat (H : Bits m → RoundTree n N M) : Prop :=
  ∀ (G : Bits n → Bits N) (x : Bits m), (queriesOf G (H x)).flatten.Nodup

end StretchDepth


