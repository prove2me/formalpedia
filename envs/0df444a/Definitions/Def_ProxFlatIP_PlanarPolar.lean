-- Prove2me | Definitions.Def_ProxFlatIP_PlanarPolar
-- name    : ProxFlatIP_PlanarPolar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:20.644537+00:00
-- url     : https://prove2.me/theorems/9161ea0c-d136-4e6b-aa8a-8e76f59406e9
-- title:
--   The rotation $\tau$, polars, polygons, $P_v$ and $\operatorname{stell}(P)$
-- statement:
--   All sets here lie in $\mathbb R^2$.
--
--   1. $\tau(x_1,x_2):=(-x_2,x_1)$ is the $90^\circ$ counterclockwise rotation, so that $(\tau v)^\top x=\det(v,x)$.
--   2. The **polar** of $Q$ is $Q^\circ:=\{x: y^\top x\le1\text{ for all }y\in Q\}$.
--   3. A **polygon** is the convex hull of a finite set, and $V(P)$ is its set of extreme points. It is **symmetric** if $-P=P$.
--   4. For $v\in\mathbb R^2$: $L_v:=\{x:(\tau v)^\top x=1\}$, $H_v:=\{x:(\tau v)^\top x\le1\}$ and $S_v:=\{x:|(\tau v)^\top x|\le1\}$.
--   5. For a symmetric polygon $P$: $P_v:=\operatorname{conv}(P\cup\{\pm v\})\cap S_v$.
--   6. When $\tau P=P^\circ$,
--   $$\operatorname{stell}(P)=\bigcup_{v\in V(P)}\ \bigcap_{w\in V(P)\setminus\{v\}}H_w,$$
--   the set of points violating at most one inequality constraint of $P$.
--
--   These objects carry the planar extremal result of Appendix A: a polygon $Q$ with $\tau Q\subseteq Q^\circ$ has a polar of area at least $3$.
--
--   **Formalization Note** The paper does not define "polygon". Here it is the convex hull of a finite subset of the plane, which may be degenerate; the condition $\tau P=P^\circ$ rules degeneracy out. The vertex count $|V(P)|$ is `Set.ncard`. Only the displayed formula for $\operatorname{stell}(P)$ is formalized, since the mission uses $\operatorname{stell}$ only under $\tau P=P^\circ$.
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, polar and τ, p.8; Definition 2, p.15; Definition 3, p.16; Definition 4, pp.17–18; "polygon" is the reading of paper.md R3

import Mathlib

open Matrix

namespace ProxFlatIP

/-! # Polygons, polars, and the planar constructions of Appendix A

Celaya–Kuhlmann–Paat–Weismantel, arXiv:2211.14941v1 (preprint): p.8 and Appendix A, pp.15–18.

**Formalization Note.** The paper does not define "polygon". Here a polygon is the convex hull of a
finite subset of `ℝ²`, so it is compact and convex, and possibly degenerate; `τP = P°` rules the
degenerate case out. `V(P)` is `Set.extremePoints ℝ P`, and `|V(P)|` is its `Set.ncard`. Areas are
`volume` on `Fin 2 → ℝ`, valued in `ℝ≥0∞`. -/

/-- The plane `ℝ²`. -/
abbrev Plane := Fin 2 → ℝ

/-- `τ : ℝ² → ℝ²`, the `90°` counterclockwise rotation (pp.1, 8), so that `(τv)⊤x = det(v,x)` (p.15). -/
def tau (x : Plane) : Plane := ![-x 1, x 0]

/-- The image `τQ` of a set. -/
def tauImage (Q : Set Plane) : Set Plane := tau '' Q

/-- The polar `Q° := {x ∈ ℝ² : y⊤x ≤ 1 for all y ∈ Q}` (p.8). The paper states it for nonempty
compact convex `Q`. -/
def polar (Q : Set Plane) : Set Plane := {x | ∀ y ∈ Q, y ⬝ᵥ x ≤ 1}

/-- A polygon: the convex hull of a finite subset of `ℝ²`. -/
def IsPolygon (P : Set Plane) : Prop := ∃ S : Set Plane, S.Finite ∧ P = convexHull ℝ S

/-- `P` is `0`-symmetric: `−P = P`. -/
def IsSymmetric (P : Set Plane) : Prop := Neg.neg '' P = P

/-- `L_v := {x ∈ ℝ² : (τv)⊤x = 1}` (Definition 2, p.15). -/
def lineL (v : Plane) : Set Plane := {x | tau v ⬝ᵥ x = 1}

/-- `H_v := {x ∈ ℝ² : (τv)⊤x ≤ 1}` (Definition 2, p.15). -/
def halfH (v : Plane) : Set Plane := {x | tau v ⬝ᵥ x ≤ 1}

/-- `S_v := {x ∈ ℝ² : |(τv)⊤x| ≤ 1}` (Definition 2, p.15). -/
def stripS (v : Plane) : Set Plane := {x | |tau v ⬝ᵥ x| ≤ 1}

/-- `P_v := conv(P ∪ {±v}) ∩ S_v` (Definition 3, p.16). -/
def modify (P : Set Plane) (v : Plane) : Set Plane :=
  convexHull ℝ (P ∪ {v, -v}) ∩ stripS v

/-- `stell(P) = ⋃_{v ∈ V(P)} ⋂_{w ∈ V(P) \ {v}} H_w` (Definition 4, pp.17–18). This is the paper's
formula for the case `τP = P°`, the only case in which this mission uses it. -/
def stell (P : Set Plane) : Set Plane :=
  ⋃ v ∈ Set.extremePoints ℝ P, ⋂ w ∈ Set.extremePoints ℝ P \ {v}, halfH w

end ProxFlatIP


