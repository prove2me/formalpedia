-- Prove2me | Definitions.Def_SteinerAPX_orthogonalRouting
-- name    : SteinerAPX_orthogonalRouting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:36:06.719931+00:00
-- url     : https://prove2.me/theorems/f7022253-d761-4a6c-a12b-9c31b372662c
-- title:
--   The orthogonal routing in $\mathbb R^{m+|U|+3}$
-- statement:
--   Let $H=(U,E)$ be a three-dimensional matching instance with $m=|U|+|E|$ gadgets. Reserve mutually orthogonal unit coordinate vectors $b_1,b_2$, one $e_s$ for each gadget $s$ and one $f_i$ for each label $i\in U\cup\{0\}$; this uses $D=m+|U|+3$ dimensions. Set $R=64$, place gadget $s$ at $z_s=Re_s$, and put the **hub** of $\Gamma_i$ at $Rf_i$. Each port labelled $i$ is $p_{s,i}=Re_s+\alpha v$ with $v\in\{\pm b_1,\pm b_2\}$ and $\alpha=1$ at a square, $\alpha=\frac23$ at a fallback. The cable $\Gamma_i$ is the union over its ports of the **branches**
--   $$
--   Re_s+\alpha v\ \longrightarrow\ Re_s+\tfrac R2 v\ \longrightarrow\ Rf_i,
--   $$
--   a gadget segment to the **bend** followed by a hub segment to the hub.
--
--   This layout is separated and has total cable length $O(m)$ (Lemma 15), which gives the constant-gap reduction in linear dimension.
--
--   **Formalization Note** The coordinates are indexed by `Bool ⊕ Gadget ⊕ Label`. The paper does not specify which corner of a square carries which label, so the port directions are a parameter: `orthogonalRoutingWith H dir` is the routing for an assignment `dir` with `IsOrthAssignment H dir` (labels of a square onto $\{\pm b_1,\pm b_2\}$, of a fallback onto $\{\pm b_1\}$), and Lemma 15 holds for every such `dir`. `orthogonalRouting H` uses one fixed choice `orthDir` (at the square of $(a,b,c)$: $0\mapsto b_1$, $(0,a)\mapsto-b_1$, $(1,b)\mapsto b_2$, $(2,c)\mapsto-b_2$; at a fallback: $0\mapsto b_1$, $u\mapsto -b_1$); this is the routing the reduction of Lemma 16 constructs.
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), §5.1, pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_SteinerAPX_CableLayout

namespace SteinerAPX

open Inst3DM CableLayout

/-- The coordinate directions of the orthogonal routing: two for `b₁, b₂`, one `e_s` per gadget,
one `f_i` per label, so `D = 2 + m + (|U| + 1) = m + |U| + 3`. -/
abbrev OrthIndex (H : Inst3DM) := Bool ⊕ Gadget H ⊕ Label H

instance (H : Inst3DM) : DecidableEq (Gadget H) := inferInstance

/-- The unit vector `b₁` of the orthogonal routing (coordinate `false`). -/
noncomputable def orthB₁ (H : Inst3DM) : EuclideanSpace ℝ (OrthIndex H) :=
  EuclideanSpace.single (Sum.inl false) 1

/-- The unit vector `b₂` of the orthogonal routing (coordinate `true`). -/
noncomputable def orthB₂ (H : Inst3DM) : EuclideanSpace ℝ (OrthIndex H) :=
  EuclideanSpace.single (Sum.inl true) 1

/-- A port assignment for the orthogonal routing, as §4.1 allows it: at the square of every
triple the four labels `0, u, v, w` are sent bijectively onto `{±b₁, ±b₂}`, and at the fallback of
every element `u` the labels `0, u` onto `{±b₁}`. -/
def IsOrthAssignment (H : Inst3DM) (dir : Gadget H → Label H → EuclideanSpace ℝ (OrthIndex H)) :
    Prop :=
  (∀ t : H.triples, Set.BijOn (dir (.inl t)) ↑(labels H (.inl t))
      ({orthB₁ H, -orthB₁ H, orthB₂ H, -orthB₂ H} : Set (EuclideanSpace ℝ (OrthIndex H)))) ∧
  (∀ u : H.Element, Set.BijOn (dir (.inr u)) ↑(labels H (.inr u))
      ({orthB₁ H, -orthB₁ H} : Set (EuclideanSpace ℝ (OrthIndex H))))

/-- **The orthogonal routing (§5.1), for a given port assignment.** S. Bartlmae,
*Inapproximability of Euclidean Steiner Tree*, STOC 2027 submission (manuscript sha256
6f78a9ea…), §5.1, pp.19–20 (PDF pp.21–22): "besides the directions b1, b2 in which the gadgets are
drawn, reserve a unit coordinate vector es for each gadget s and fi for each label i ∈ U ∪ {0},
all mutually orthogonal; this uses D = m + |U| + 3 dimensions. Set R = 64. We place each gadget s
at zs = Res, and let the hub of Γi be Rfi. Each port labelled i has the form ps,i = Res + αv, where
v ∈ {±b1, ±b2} and α = 1 for a square or α = 2/3 for a fallback. The cable has a gadget segment
from this port in direction v up to the bend Res + (R/2)v, followed by a hub segment from the bend
straight to the hub, which together form the branch Res + αv −→ Res + (R/2)v −→ Rfi. The cable Γi
is the union of these branches over all ports labelled i; we call this the orthogonal routing
(Figure 5)."

The layout lives in `ℝ^D` with coordinates indexed by `OrthIndex H`: `b₁, b₂` are the unit vectors
of the coordinates `false, true`, `e_s` and `f_i` those of `s` and `i`. The cable `Γᵢ` has, for
every gadget `s` with a port labelled `i`, the gadget segment `[p_{s,i}, R e_s + (R/2) v]` and the
hub segment `[R e_s + (R/2) v, R f_i]`, where `v = dir s i`.

**Formalization Note** The paper does not say which corner of a square carries which label: the
port directions `dir` are a parameter, and the routing is the paper's whenever `dir` is an
`IsOrthAssignment`. Values of `dir` at labels that are not labels of `s` are never used. -/
noncomputable def orthogonalRoutingWith (H : Inst3DM)
    (dir : Gadget H → Label H → EuclideanSpace ℝ (OrthIndex H)) :
    CableLayout H (EuclideanSpace ℝ (OrthIndex H)) :=
  let R : ℝ := 64
  let e : Gadget H → EuclideanSpace ℝ (OrthIndex H) := fun s =>
    EuclideanSpace.single (Sum.inr (Sum.inl s)) 1
  let f : Label H → EuclideanSpace ℝ (OrthIndex H) := fun i =>
    EuclideanSpace.single (Sum.inr (Sum.inr i)) 1
  { z := fun s => R • e s
    b₁ := orthB₁ H
    b₂ := orthB₂ H
    dir := dir
    cable := fun i => by
      classical
      exact (Finset.univ.filter fun s => i ∈ labels H s).biUnion fun s =>
        {(R • e s + alpha s • dir s i, R • e s + (R / 2) • dir s i),
         (R • e s + (R / 2) • dir s i, R • f i)} }

/-- One fixed port assignment: at the square of the triple `(a, b, c)`, label `0 ↦ b₁`,
`(0,a) ↦ −b₁`, `(1,b) ↦ b₂`, `(2,c) ↦ −b₂`; at a fallback, `0 ↦ b₁`, `u ↦ −b₁`. -/
noncomputable def orthDir (H : Inst3DM) : Gadget H → Label H → EuclideanSpace ℝ (OrthIndex H) :=
  fun s i =>
    match s, i with
    | .inl _, none => orthB₁ H
    | .inl _, some (k, _) => if k = 0 then -orthB₁ H else if k = 1 then orthB₂ H else -orthB₂ H
    | .inr _, none => orthB₁ H
    | .inr _, some _ => -orthB₁ H

/-- **The orthogonal routing (§5.1) with the fixed port assignment `orthDir`.** Same source as
`orthogonalRoutingWith`; this is the routing the reduction of Lemma 16 constructs.

**Formalization Note** Lemma 15 is stated for `orthogonalRoutingWith H dir` and every
`IsOrthAssignment dir`; this fixed choice is one of them. -/
noncomputable def orthogonalRouting (H : Inst3DM) : CableLayout H (EuclideanSpace ℝ (OrthIndex H)) :=
  orthogonalRoutingWith H (orthDir H)

end SteinerAPX


