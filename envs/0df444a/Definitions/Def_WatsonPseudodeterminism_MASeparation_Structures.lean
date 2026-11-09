-- Prove2me | Definitions.Def_WatsonPseudodeterminism_MASeparation_Structures
-- name    : WatsonPseudodeterminism_MASeparation_Structures
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:31:21.367686+00:00
-- url     : https://prove2.me/theorems/a8583260-4a96-4428-ae23-58cd37baab71
-- title:
--   Consistent block structures and conditional balance
-- statement:
--   A structure is a triple $(a,b,c)$ of partial assignments. At each coordinate all three assignments are absent, or all are present as complete blocks $a_i,b_i$ and a bit $c_i=g(a_i,b_i)$. Its width $w$ counts assigned coordinates. A string $z$ agrees with the structure when it equals $c_i$ wherever $c_i$ is assigned.
--
--   The rectangle $S^{a,b}$ is constructed from all block inputs agreeing with $a$ and $b$. A rectangle $R$ is $(a,b,c)$-balanced when $R\subseteq S^{a,b}$ and, for every agreeing $z$,
--
--   $$\frac{|R|}{1.01\,2^{m-w}}\le |R_z|\le1.01\frac{|R|}{2^{m-w}}.$$
--
--   There are at most $m$ assigned coordinates, so natural subtraction in $m-w$ is exact. Options on whole blocks encode the source's totally assigned or totally unassigned alternatives; they exclude partially fixed blocks. These definitions provide the conditioning interface for Lemma 3.
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §2.2, p. 7 (structures, S^{a,b} and (a,b,c)-balanced); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Balance

namespace WatsonPseudodeterminism.MASeparation

/-- §2.2, p. 7: blocks are either entirely fixed consistently, or entirely unassigned. -/
structure GadgetStructure (h m : ℕ) where
  a : Fin m → Option (Block h)
  b : Fin m → Option (Block h)
  c : Fin m → Option Bool
  consistent : ∀ i,
    (a i = none ∧ b i = none ∧ c i = none) ∨
    ∃ x y, a i = some x ∧ b i = some y ∧ c i = some (gadget x y)

noncomputable def GadgetStructure.width {h m : ℕ} (s : GadgetStructure h m) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => s.c i ≠ none)).card

/-- z agrees with all assigned coordinates of c. -/
def GadgetStructure.Agrees {h m : ℕ} (s : GadgetStructure h m) (z : Fin m → Bool) : Prop :=
  ∀ i b, s.c i = some b → z i = b

/-- The rectangle S^{a,b}, constructed from the structure's partial assignments. -/
noncomputable def GadgetStructure.rectangle {h m : ℕ} (s : GadgetStructure h m) :
    GadgetRectangle h m := by
  classical
  exact (Finset.univ.filter (fun x => ∀ i u, s.a i = some u → x i = u),
    Finset.univ.filter (fun y => ∀ i v, s.b i = some v → y i = v))

/-- (a,b,c)-balance includes containment in S^{a,b} and both factor bounds. -/
def StructureBalanced {h m : ℕ} (R : GadgetRectangle h m) (s : GadgetStructure h m) : Prop :=
  Subrectangle R s.rectangle ∧ ∀ z, s.Agrees z →
    WithinFactor ((slice R z).card : ℝ) ((rectPoints R).card / (2 : ℝ) ^ (m - s.width))

end WatsonPseudodeterminism.MASeparation


