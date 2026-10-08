-- Prove2me | Definitions.Def_FreeIsing
-- name    : FreeIsing
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:12.088798+00:00
-- url     : https://prove2.me/theorems/cfa6f6fa-ab18-49eb-a36a-8a93cd07d470
-- statement:
--   TreeVertex(d) is the set of vertices of the d-regular rooted-at-empty-word tree, namely finite words over the alphabet {0,…,d−1} in which no two consecutive letters are equal. Two vertices are treeAdj-adjacent when one is obtained from the other by appending a single letter. A TreeAut(d) is a bijection of the vertex set that preserves and reflects this adjacency, i.e. a graph automorphism of the tree, and relabel(g,x) transports a configuration x on vertices by g, sending v to x(g⁻¹v). IsingSpin has two values, neg and pos, with the discrete (all subsets measurable) σ-algebra. uniform01 is Lebesgue measure restricted to [0,1], a probability measure, and labelMeasure(d) is the infinite product of copies of it over the vertices, modelling i.i.d. uniform labels. A finite vertex set D is ConnectedFinset if it is nonempty and any two of its points are joined by a path of adjacent vertices staying inside D. inducedEdges(D) lists the adjacent pairs inside D, each once, oriented from the shorter word to the longer. For a parameter θ, freeCylinderWeight(θ,D,η) is the nonnegative real part of (1/2)·∏ over induced edges of (1+θ)/2 if the endpoint spins of η agree and (1−θ)/2 if they differ. HasFreeIsingLaw(θ,μ) says that a measure μ on spin configurations assigns to every cylinder event {x : x=η on D}, for every connected finite D and every η, exactly this weight; this is the free Ising Markov specification with edge correlation θ and uniform one-vertex marginals. IsFactorOfIID(d,θ) is the defined proposition that there is a measurable map Φ from label configurations to spin configurations such that the pushforward of labelMeasure(d) under Φ has the free Ising law with parameter θ, and for every tree automorphism g, almost surely in the labels U, Φ(relabel g U)=relabel g (Φ U), so Φ is automorphism-equivariant.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FreeIsing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FreeIsing.lean; bytes 16..2809
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

abbrev TreeVertex (d : ℕ) :=
  {word : List (Fin d) // List.IsChain (fun first second : Fin d => first ≠ second) word}

def treeAdj {d : ℕ} (u v : TreeVertex d) : Prop :=
  (∃ c : Fin d, v.1 = u.1 ++ [c]) ∨
  (∃ c : Fin d, u.1 = v.1 ++ [c])

structure TreeAut (d : ℕ) where
  toEquiv : TreeVertex d ≃ TreeVertex d
  map_adj : ∀ u v, treeAdj (toEquiv u) (toEquiv v) ↔ treeAdj u v

def relabel {d : ℕ} {α : Type*} (g : TreeAut d)
    (x : TreeVertex d → α) : TreeVertex d → α :=
  fun v => x (g.toEquiv.symm v)

inductive IsingSpin where
  | neg
  | pos
  deriving DecidableEq

protected abbrev IsingSpin.enumList : List IsingSpin := [.neg, .pos]

protected theorem IsingSpin.enumList_getElem?_ctorIdx_eq (x : IsingSpin) :
    IsingSpin.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem IsingSpin.enumList_nodup : IsingSpin.enumList.Nodup := by decide

instance : Fintype IsingSpin where
  elems := ⟨IsingSpin.enumList, IsingSpin.enumList_nodup⟩
  complete x := by cases x <;> decide

instance isingSpinMeasurable : MeasurableSpace IsingSpin := ⊤

def uniform01 : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

instance uniform01Probability : IsProbabilityMeasure uniform01 where
  measure_univ := by simp [uniform01]

def labelMeasure (d : ℕ) : Measure (TreeVertex d → ℝ) := by
  classical
  exact Measure.infinitePi (fun _ : TreeVertex d => uniform01)

def ConnectedFinset {d : ℕ} (D : Finset (TreeVertex d)) : Prop :=
  D.Nonempty ∧
    ∀ u ∈ D, ∀ v ∈ D,
      Relation.ReflTransGen
        (fun x y : TreeVertex d => x ∈ D ∧ y ∈ D ∧ treeAdj x y) u v

def inducedEdges {d : ℕ} (D : Finset (TreeVertex d)) :
    Finset (TreeVertex d × TreeVertex d) := by
  classical
  exact (D.product D).filter (fun e =>
    treeAdj e.1 e.2 ∧ e.1.1.length < e.2.1.length)

def freeCylinderWeight {d : ℕ} (theta : ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) : ENNReal :=
  ENNReal.ofReal
    ((1 / 2 : ℝ) *
      Finset.prod (inducedEdges D) (fun e =>
        (1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2))

def HasFreeIsingLaw {d : ℕ} (theta : ℝ)
    (mu : Measure (TreeVertex d → IsingSpin)) : Prop :=
  ∀ (D : Finset (TreeVertex d)), ConnectedFinset D →
    ∀ eta : TreeVertex d → IsingSpin,
      mu {x | ∀ v ∈ D, x v = eta v} = freeCylinderWeight theta D eta

def IsFactorOfIID (d : ℕ) (theta : ℝ) : Prop :=
  ∃ Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin),
    Measurable Phi ∧
    HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)) ∧
    ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U)



end Problem367
end
end OAI


