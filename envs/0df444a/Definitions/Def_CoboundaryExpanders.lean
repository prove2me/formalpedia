-- Prove2me | Definitions.Def_CoboundaryExpanders
-- name    : CoboundaryExpanders
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:04.336989+00:00
-- url     : https://prove2.me/theorems/2c930bb9-2b59-40fc-a748-3c29bdda3f0b
-- statement:
--   A finite abstract simplicial complex consists of a finite labelled vertex set and a collection of faces containing the empty face and every singleton and closed under taking subsets. Its i-dimensional faces have i+1 vertices. It is pure of dimension s if s-dimensional faces exist and every face lies in one, and connected if its vertex set is nonempty and any two vertices are joined by an edge path. An i-cochain assigns an element of F₂ to each i-face. Relative to dimension s, an i-face has weight equal to its number of incident s-faces divided by the product of the total number of s-faces and binomial(s+1,i+1); the weighted support norm sums these weights over faces where a cochain is nonzero. The coboundary of an i-cochain sums its values on the i-faces of each (i+1)-face over F₂. The space B⁰ consists of constant cochains, and Bⁱ for i>0 consists of coboundaries from degree i−1. Distance to a set of cochains is the infimum of the weighted norms of differences. MainStatement is the defined proposition that, for every integer d≥3, there exist a natural number D, a real ε>0, and a sequence of connected pure d-dimensional complexes whose vertex counts tend to infinity, such that each vertex belongs to at most D top-dimensional faces and, for every complex in the sequence, every 0≤i<d, and every i-cochain f, ‖δf‖≥ε·dist(f,Bⁱ), using weights relative to dimension d. The constants D and ε are uniform across the sequence and all these degrees and cochains.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoboundaryExpanders.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CoboundaryExpanders.lean; bytes 16..3409
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
# Bounded-degree coboundary expanders in every dimension

Finite connected pure complexes with uniformly bounded top-face incidence and
uniform weighted coboundary expansion over F₂ in all degrees below the dimension.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace CoboundaryExpanders

/-- A finite abstract simplicial complex with every labelled vertex present. -/
structure Complex where
  vertexCount : ℕ
  faces : Finset (Finset (Fin vertexCount))
  empty_mem : ∅ ∈ faces
  downward : ∀ {σ τ}, σ ∈ faces → τ ⊆ σ → τ ∈ faces
  vertex_mem : ∀ v, {v} ∈ faces

namespace Complex

/-- Faces of dimension `i` have exactly `i + 1` vertices. -/
def facesOf (X : Complex) (i : ℕ) : Finset (Finset (Fin X.vertexCount)) :=
  X.faces.filter (fun σ => σ.card = i + 1)

def Face (X : Complex) (i : ℕ) := {σ // σ ∈ X.facesOf i}

instance (X : Complex) (i : ℕ) : Fintype (X.Face i) := Subtype.fintype _
instance (X : Complex) (i : ℕ) : DecidableEq (X.Face i) := Classical.decEq _

/-- Exact purity: top faces exist and every face lies in a top face. -/
def Pure (X : Complex) (s : ℕ) : Prop :=
  (X.facesOf s).Nonempty ∧
  ∀ σ ∈ X.faces, ∃ τ ∈ X.facesOf s, σ ⊆ τ

/-- Connectedness of the nonempty one-skeleton. -/
def Connected (X : Complex) : Prop :=
  Nonempty (Fin X.vertexCount) ∧
  ∀ v w : Fin X.vertexCount,
    Relation.ReflTransGen (fun a b => a ≠ b ∧ {a, b} ∈ X.faces) v w

abbrev Cochain (X : Complex) (i : ℕ) := X.Face i → ZMod 2

/-- Weights are normalized counts of incident top-dimensional faces. -/
def weight (X : Complex) (s i : ℕ) (σ : X.Face i) : ℝ :=
  (((X.facesOf s).filter (fun τ => σ.val ⊆ τ)).card : ℝ) /
    ((Nat.choose (s + 1) (i + 1) : ℝ) * (X.facesOf s).card)

/-- Weighted support norm. -/
def norm (X : Complex) (s i : ℕ) (f : X.Cochain i) : ℝ :=
  ∑ σ : X.Face i, if f σ ≠ 0 then X.weight s i σ else 0

/-- Simplicial coboundary over F₂. -/
def coboundary (X : Complex) (i : ℕ) (f : X.Cochain i) : X.Cochain (i + 1) :=
  fun τ => ∑ σ : X.Face i, if σ.val ⊆ τ.val then f σ else 0

/-- Actual coboundaries, with constant cochains in degree zero. -/
def coboundaries (X : Complex) : (i : ℕ) → Set (X.Cochain i)
  | 0 => {f | ∃ c : ZMod 2, f = fun _ => c}
  | i + 1 => Set.range (X.coboundary i)

/-- Distance in the weighted support norm; on a nonempty finite set it is a minimum. -/
def distance (X : Complex) (s i : ℕ) (f : X.Cochain i)
    (A : Set (X.Cochain i)) : ℝ :=
  sInf ((fun a => X.norm s i (f - a)) '' A)

/-- Number of top-dimensional faces incident to a vertex. -/
def topDegree (X : Complex) (s : ℕ) (v : Fin X.vertexCount) : ℕ :=
  ((X.facesOf s).filter (fun τ => v ∈ τ)).card

end Complex

/-- Both constants are uniform over the sequence, all degrees below `d`, and all cochains. -/
def MainStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    ∃ (D : ℕ) (ε : ℝ), 0 < ε ∧
      ∃ X : ℕ → Complex,
        (∀ m, (X m).Pure d ∧ (X m).Connected) ∧
        Tendsto (fun m => ((X m).facesOf 0).card) atTop atTop ∧
        (∀ m (v : Fin (X m).vertexCount), (X m).topDegree d v ≤ D) ∧
        ∀ m i, i < d → ∀ f : (X m).Cochain i,
          ε * (X m).distance d i f ((X m).coboundaries i) ≤
            (X m).norm d (i + 1) ((X m).coboundary i f)



end CoboundaryExpanders
end
end OAI


