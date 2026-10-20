-- Prove2me | Definitions.Def_Esgk_EquidistantWitnessCounts
-- name    : Esgk_EquidistantWitnessCounts
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-20T05:03:51.312476+00:00
-- url     : https://prove2.me/theorems/0da15d46-00c8-44ca-8343-a8321d29daae
-- title:
--   Equidistant witnesses and distance-degree counts
-- statement:
--   For an indexed configuration $p=(p_1,\dots,p_n)$ of points in the plane, let $R(p)=\{|p_i-p_j|: i\ne j\}$ be its set of distance values and $d_r(x)=\#\{j\ne x: |p_x-p_j|=r\}$ the number of configuration points at distance $r$ from $p_x$ (the public definitions `OrderedDistanceValues` and `DistanceOutNeighborsAtValue`). This module defines five counting objects.
--
--   1. `EquidistantWitnesses P a b`: for a finite set $P\subset\mathbb R^2$ and points $a,b$, the points $x\in P$ with $|x-a|=|x-b|$.
--   2. `IndexedEquidistantWitnesses p i j`: the indices $x$ with $|p_x-p_i|=|p_x-p_j|$.
--   3. `OrderedPairWitnessTotal p`: the sum of the sizes of these index sets over all ordered pairs $(i,j)$ of distinct indices,
--   $$
--   \sum_{i\ne j}\#\{\,x:\ |p_x-p_i|=|p_x-p_j|\,\}.
--   $$
--   4. `ApexEqualDistancePairs p x`: the ordered pairs $(a,b)$ of distinct indices, both different from $x$, with $|p_x-p_a|=|p_x-p_b|$.
--   5. `DistanceDegreeFallingMass p`: the sum
--   $$
--   \sum_{r\in R(p)}\ \sum_{x} d_r(x)\bigl(d_r(x)-1\bigr).
--   $$
--
--   For an injective configuration the witness total equals the falling mass: both count the triples $(x,a,b)$ of indices with $a\ne b$ and $|p_x-p_a|=|p_x-p_b|$. These counts compare equidistant witnesses with the number of distinct distances.
--
--   **Formalization Note** Indices are elements of `Fin n`. In the falling mass, $d_r(x)-1$ is natural-number subtraction; the product is $0$ when $d_r(x)=0$ in either convention.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Esgk_DistanceDesign
import Definitions.Def_Esgk_Energy
import Definitions.Def_Esgk_Foundation

namespace Esgk

open EuclideanGeometry
open scoped BigOperators
variable {α : Type*}

noncomputable def EquidistantWitnesses (P : Finset Point) (a b : Point) : Finset Point :=
  P.filter (fun x => dist x a = dist x b)

noncomputable def IndexedEquidistantWitnesses {n : ℕ}
    (p : Config n) (i j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun x => dist (p x) (p i) = dist (p x) (p j))

noncomputable def OrderedPairWitnessTotal {n : ℕ} (p : Config n) : ℕ :=
  ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
    (IndexedEquidistantWitnesses p ij.1 ij.2).card

noncomputable def ApexEqualDistancePairs {n : ℕ}
    (p : Config n) (x : Fin n) : Finset (Fin n × Fin n) :=
  ((Finset.univ.erase x).offDiag).filter
    (fun ab => dist (p x) (p ab.1) = dist (p x) (p ab.2))

noncomputable def DistanceDegreeFallingMass {n : ℕ} (p : Config n) : ℕ :=
  ∑ r ∈ OrderedDistanceValues p,
    ∑ x, (DistanceOutNeighborsAtValue p x r).card *
      ((DistanceOutNeighborsAtValue p x r).card - 1)

end Esgk


