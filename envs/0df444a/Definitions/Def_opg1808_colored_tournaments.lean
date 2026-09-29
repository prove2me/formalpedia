-- Prove2me | Definitions.Def_opg1808_colored_tournaments
-- name    : opg1808_colored_tournaments
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-07T07:14:03.252731+00:00
-- url     : https://prove2.me/theorems/ade5ecba-e525-46e2-a90f-33719b82967d
-- title:
--   Three-colored tournaments and monochromatic reachability
-- statement:
--   This module models a tournament as a loopless binary relation with exactly one directed arc between every two distinct vertices. An arc coloring has three labeled colors; only colors of actual arcs matter.
--
--   A rainbow directed triangle is a cyclically oriented triangle whose three arc colors are pairwise distinct. A vertex $s$ monochromatically reaches $t$ when some one color supports a directed path from $s$ to $t$. Reachability is reflexive, so the path may have length zero when $s=t$. A monochromatic source reaches every target in this sense, and the chosen path color may depend on the target.
-- source:
--   Open Problem Garden, Monochromatic reachability versus rainbow triangles, https://www.openproblemgarden.org/op/monochromatic_reachability_vs_rainbow_triangles

import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation

namespace OPG1808

universe u

abbrev Digraph (V : Type u) := V → V → Prop
abbrev ArcColoring (V : Type u) := V → V → Fin 3

/-- A loopless orientation of every pair of distinct vertices. -/
def IsTournament {V : Type u} (D : Digraph V) : Prop :=
  (∀ v : V, ¬ D v v) ∧
  ∀ ⦃u v : V⦄, u ≠ v →
    (D u v ∨ D v u) ∧ ¬ (D u v ∧ D v u)

/-- A rainbow directed triangle follows the displayed cyclic orientation and
uses three pairwise distinct arc colors. -/
def HasRainbowDirectedTriangle {V : Type u} (D : Digraph V)
    (color : ArcColoring V) : Prop :=
  ∃ a b c : V,
    a ≠ b ∧ b ≠ c ∧ c ≠ a ∧
    D a b ∧ D b c ∧ D c a ∧
    color a b ≠ color b c ∧
    color b c ≠ color c a ∧
    color c a ≠ color a b

/-- There is a directed path from `s` to `t` whose arcs all have one color.
The chosen color may depend on the ordered pair. -/
def MonochromaticallyReaches {V : Type u} (D : Digraph V)
    (color : ArcColoring V) (s t : V) : Prop :=
  ∃ k : Fin 3,
    Relation.ReflTransGen (fun x y => D x y ∧ color x y = k) s t

/-- A vertex reaches every vertex by a monochromatic directed path; different
targets may use different colors. -/
def IsMonochromaticSource {V : Type u} (D : Digraph V)
    (color : ArcColoring V) (s : V) : Prop :=
  ∀ t : V, MonochromaticallyReaches D color s t

end OPG1808


