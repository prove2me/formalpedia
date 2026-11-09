-- Prove2me | Definitions.Def_RamseyDisambig_Spherical_DihedralAction
-- name    : RamseyDisambig_Spherical_DihedralAction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:31:19.901768+00:00
-- url     : https://prove2.me/theorems/986f6510-2b62-456f-b2e8-91ea59f37c10
-- title:
--   The dihedral action on cycle vertices
-- statement:
--   For each positive side length $R$, the dihedral group acts on $\mathbb Z_R$ by rotations and reflections. In Mathlib's group parametrization the action is
--   $$r_i\cdot x=x-i,\qquad s r_i\cdot x=i-x.$$
--   Thus the geometric rotation $x\mapsto x+i$ is labeled $r_{-i}$. The reflection formula has the same parameter as on the cycle.
--
--   This action supports the diagonal action on ordered pairs used in the proof of Lemma 12; it imposes no hypothesis on the coloring. The change of rotation label is necessary because Mathlib defines $r_i s r_j=s r_{j-i}$. The underlying permutations are exactly all rotations and reflections appearing in the source.
--
--   **Formalization Note** This is an explicit action structure, not a global instance. Its action laws are elementary algebra. A separate verification example checks solvability of the underlying dihedral group as an extension of two abelian groups; no theorem conclusion is placed in this definition.
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), §2.2, pp. 11–12 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Torus

set_option autoImplicit false

namespace RamseyDisambig.Spherical

/-- Mathlib's `r i * sr j = sr (j-i)` uses the opposite rotation parameter.
Thus rotation by +i is `r (-i)`, while `sr i` is reflection x ↦ i-x.
This is the cycle action used on p. 12, with a change only of group labels. -/
abbrev dihedralCycleAction (R : ℕ+) : MulAction (DihedralGroup (R : ℕ)) (ZMod (R : ℕ)) where
  smul g x := match g with
    | .r i => x - i
    | .sr i => i - x
  one_smul x := by change x - 0 = x; exact sub_zero x
  mul_smul g h x := by
    cases g with
    | r a =>
      cases h with
      | r b => change x - (a + b) = (x - b) - a; ring
      | sr b => change (b - a) - x = (b - x) - a; ring
    | sr a =>
      cases h with
      | r b => change (a + b) - x = a - (x - b); ring
      | sr b => change x - (b - a) = a - (b - x); ring

end RamseyDisambig.Spherical


