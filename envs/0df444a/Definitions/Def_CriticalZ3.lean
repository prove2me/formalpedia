-- Prove2me | Definitions.Def_CriticalZ3
-- name    : CriticalZ3
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:06.439095+00:00
-- url     : https://prove2.me/theorems/0b000ddd-9ea0-4e4b-a743-f64e0e42ba30
-- statement:
--   The vertices are the integer lattice ℤ³, and a bond is indexed by a vertex x and one of the three coordinate directions, representing the edge from x to x+eᵢ. Bond configurations assign a Boolean value to each bond, and site configurations assign one to each vertex, with true meaning open. Two vertices are nearest neighbors when they differ by one unit in a single coordinate. An open bond joins its two endpoints in either direction; an open site edge joins nearest neighbors whose two sites are open. Bond connectivity means there is a finite path of open bonds, allowing the path of length zero. Site connectivity additionally requires the starting site to be open and uses finite paths of open site edges. The corresponding cluster at x consists of vertices connected to x; a closed site has an empty site cluster, whereas every bond cluster contains its starting vertex. The infinite-cluster events consist of configurations whose respective cluster at x is infinite. For any real p, the parameter is clamped to max(0,min(1,p)), and the bond and site laws are independent product Bernoulli measures with this probability of being open. The bond and site critical probabilities are defined separately as the infima of the p in [0,1] for which the corresponding law gives positive probability to an infinite cluster at the origin.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CriticalZ3.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CriticalZ3.lean; bytes 16..1944
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory

namespace CriticalZ3

abbrev Vertex := Fin 3 → ℤ
abbrev Bond := Vertex × Fin 3
abbrev BondConfig := Bond → Bool
abbrev SiteConfig := Vertex → Bool

def step (x : Vertex) (i : Fin 3) : Vertex := fun j => x j + if i = j then 1 else 0

def NearestNeighbor (x y : Vertex) : Prop :=
  ∃ i : Fin 3, y = step x i ∨ x = step y i

def BondOpen (ω : BondConfig) (x y : Vertex) : Prop :=
  (∃ i : Fin 3, y = step x i ∧ ω (x, i) = true) ∨
  (∃ i : Fin 3, x = step y i ∧ ω (y, i) = true)

def SiteOpen (ω : SiteConfig) (x y : Vertex) : Prop :=
  NearestNeighbor x y ∧ ω x = true ∧ ω y = true

def BondConnected (ω : BondConfig) (x y : Vertex) : Prop :=
  Relation.ReflTransGen (BondOpen ω) x y

def SiteConnected (ω : SiteConfig) (x y : Vertex) : Prop :=
  ω x = true ∧ Relation.ReflTransGen (SiteOpen ω) x y

def bondCluster (ω : BondConfig) (x : Vertex) : Set Vertex :=
  {y | BondConnected ω x y}

def siteCluster (ω : SiteConfig) (x : Vertex) : Set Vertex :=
  {y | SiteConnected ω x y}

def bondInfiniteAt (x : Vertex) : Set BondConfig := {ω | (bondCluster ω x).Infinite}
def siteInfiniteAt (x : Vertex) : Set SiteConfig := {ω | (siteCluster ω x).Infinite}

noncomputable def parameter (p : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 p), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

noncomputable def bondLaw (p : ℝ) : Measure BondConfig :=
  Measure.infinitePi (fun _ : Bond => bernoulliMeasure true false (parameter p))

noncomputable def siteLaw (p : ℝ) : Measure SiteConfig :=
  Measure.infinitePi (fun _ : Vertex => bernoulliMeasure true false (parameter p))

noncomputable def bondCritical : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < bondLaw p (bondInfiniteAt 0)}

noncomputable def siteCritical : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < siteLaw p (siteInfiniteAt 0)}



end CriticalZ3
end OAI


