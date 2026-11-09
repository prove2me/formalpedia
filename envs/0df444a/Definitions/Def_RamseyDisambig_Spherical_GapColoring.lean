-- Prove2me | Definitions.Def_RamseyDisambig_Spherical_GapColoring
-- name    : RamseyDisambig_Spherical_GapColoring
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:21:45.567858+00:00
-- url     : https://prove2.me/theorems/cc738dff-d4f1-4a0b-97b0-1a1e10b6a676
-- title:
--   Finite diameter and gap colorings
-- statement:
--   Let $X$ be a finite set with a real distance function $d$. Its diameter is
--   $$D=\sup\{d(x,y):x,y\in X\},$$
--   with $D=0$ for the empty set. For a metric distance and $0<\varepsilon<1/2$, a binary coloring $c:X\times X\to\{0,1\}$ is an $\varepsilon$-gap coloring when
--   $$d(x,y)\le\varepsilon D\ \Longrightarrow\ c(x,y)=0,\qquad d(x,y)\ge(1-\varepsilon)D\ \Longrightarrow\ c(x,y)=1.$$
--   The predicate records exactly the two endpoint prescriptions. It does not impose symmetry or constrain intermediate pairs. It is shared by the torus statements and the gap-preservation lemma.
--
--   **Formalization Note** A `Finite` instance bounds the range of the real supremum. The definition accepts a distance function directly; the theorem on general spaces supplies metric-space instances, and the cube and torus use their specified metric distances. A nonempty space of zero diameter has no gap coloring, since the two prescriptions conflict. The empty space has the empty coloring and zero diameter.
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), §2.1, p. 8 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Mathlib

set_option autoImplicit false

noncomputable section

namespace RamseyDisambig.Spherical

/-- Diameter for a finite distance space; empty spaces have diameter zero. Source p. 8.
The range is finite, so the real supremum never encounters an unbounded set. -/
def finiteDiameter {X : Type*} [Finite X] (d : X → X → ℝ) : ℝ :=
  sSup (Set.range (fun p : X × X => d p.1 p.2))

/-- The two endpoint prescriptions of an ε-gap coloring, p. 8.
All applications use metric distances and 0 < ε < 1/2. -/
def GapColoring {X : Type*} [Finite X] (ε : ℝ) (d : X → X → ℝ)
    (c : X → X → Bool) : Prop :=
  (∀ x y, d x y ≤ ε * finiteDiameter d → c x y = false) ∧
  (∀ x y, (1 - ε) * finiteDiameter d ≤ d x y → c x y = true)

end RamseyDisambig.Spherical


