-- Prove2me | Definitions.Def_TorsionFreeHyperbolic
-- name    : TorsionFreeHyperbolic
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:15.775987+00:00
-- url     : https://prove2.me/theorems/18ee94a5-fd34-479d-bba1-aea511730e9b
-- statement:
--   TorsionFree(G) for a group G means that every element g with g^n = 1 for some positive integer n is the identity; the docstring notes this does not assert unique roots. For a simple graph X, a walk p from x to y is a Geodesic when its length equals the graph distance between x and y, i.e. it is a shortest edge path. For a natural number δ and three walks p from x to y, q from y to z and r from z to x, SideThin(X,δ,p,q,r) says that every vertex a on p lies within graph distance δ of some vertex on q or on r. WordHyperbolic(G) is the property that there exist a finite subset S of G whose multiplicative Cayley graph (the simple graph mulCayley S) is connected, which the source says expresses that S generates G, and a natural number δ such that for all x, y, z in G and all walks p from x to y, q from y to z and r from z to x in that graph, if all three walks are geodesics then each side is δ-thin with respect to the other two: SideThin holds for (p,q,r), for (q,r,p) and for (r,p,q). These are definitions only, and no result relating torsion-freeness and hyperbolicity is stated.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TorsionFreeHyperbolic.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TorsionFreeHyperbolic.lean; bytes 16..1478
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace Release075

universe u v

/-- No nonidentity element has finite order. This does not assert unique roots. -/
def TorsionFree (G : Type u) [Group G] : Prop :=
  ∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1

/-- A shortest edge path in the unit-edge graph. -/
def Geodesic {V : Type u} (X : SimpleGraph V) {x y : V} (p : X.Walk x y) : Prop :=
  p.length = X.dist x y

/-- Each vertex of `p` is within `δ` of a vertex of `q` or `r`. -/
def SideThin {V : Type u} (X : SimpleGraph V) (δ : ℕ) {x y z : V}
    (p : X.Walk x y) (q : X.Walk y z) (r : X.Walk z x) : Prop :=
  ∀ a ∈ p.support, ∃ b, (b ∈ q.support ∨ b ∈ r.support) ∧ X.dist a b ≤ δ

/-- A finitely generated group with a unit-edge Cayley graph whose geodesic triangles
are uniformly thin. Connectedness of this Cayley graph asserts that `S` generates. -/
def WordHyperbolic (G : Type u) [Group G] : Prop :=
  ∃ S : Set G, S.Finite ∧ (SimpleGraph.mulCayley S).Connected ∧
    ∃ δ : ℕ, ∀ (x y z : G)
      (p : (SimpleGraph.mulCayley S).Walk x y)
      (q : (SimpleGraph.mulCayley S).Walk y z)
      (r : (SimpleGraph.mulCayley S).Walk z x),
      Geodesic (SimpleGraph.mulCayley S) p →
      Geodesic (SimpleGraph.mulCayley S) q →
      Geodesic (SimpleGraph.mulCayley S) r →
      SideThin (SimpleGraph.mulCayley S) δ p q r ∧
      SideThin (SimpleGraph.mulCayley S) δ q r p ∧
      SideThin (SimpleGraph.mulCayley S) δ r p q



end Release075
end OAI


