-- Prove2me | Definitions.Def_Submission_ThreeSum_HashFamily
-- name    : Submission_ThreeSum_HashFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:38:25.783006+00:00
-- url     : https://prove2.me/theorems/ed7ed9b8-a45f-40ed-9dd2-91b05ff2fe1a
-- title:
--   Hash Family
-- statement:
--   Definitions and structural lemmas for Hash Family, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
def oneHot [Zero K] [One K] (s : α → Bool) : α × Bool → K :=
  fun p => if s p.1 = p.2 then 1 else 0
section Relations
variable [Ring K]
end Relations
section LinearIndependence
variable [Field K]
end LinearIndependence
section UniformFibers
variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]
noncomputable def hashMap (v : ι → σ → K) : (σ → K) →ₗ[K] (ι → K) := by
  classical
  exact LinearMap.pi (fun i => dotProductEquiv K σ (v i))
end UniformFibers
section ActualHashes
variable {ι : Type*} [Fintype α] [Field K]
def hashValue (w : α × Bool → K) (s : α → Bool) : K :=
  ∑ i, w (i, s i)
end ActualHashes
section WordEvents
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
noncomputable def eventProbability {Ω : Type*} [Fintype Ω] (A : Finset Ω) : ℝ :=
  (A.card : ℝ) / Fintype.card Ω
def wordEvent {r : ℕ} (words : Fin r → α → Bool) (target : Fin r → K) :
    Finset (α × Bool → K) :=
  Finset.univ.filter (fun w => ∀ i, hashValue w (words i) = target i)
def pairEvent (s t : α → Bool) (a b : K) : Finset (α × Bool → K) :=
  Finset.univ.filter (fun w => hashValue w s = a ∧ hashValue w t = b)
end WordEvents
section IncidenceCounting
variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]
def incidenceCount (events : E → Finset Ω) (w : Ω) : ℕ :=
  (Finset.univ.filter (fun e => w ∈ events e)).card
end IncidenceCounting
section GraphMoments
variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
def outputMask (left right : E → α → Bool) (e : E) : α → Bool :=
  fun i => left e i == right e i
def badPartners (left right : E → α → Bool) (e : E) : Finset E :=
  Finset.univ.filter (fun f => left e = left f ∨ right e = right f ∨
    outputMask left right e = outputMask left right f)
end GraphMoments
section SeparableTrimming
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
def bucketSize (vertices : Finset (α → Bool)) (w : α × Bool → K) (target : K) : ℕ :=
  (vertices.filter (fun s => hashValue w s = target)).card
def loadedPairMass (s t : α → Bool) (a b : K) (vertices : Finset (α → Bool)) : ℕ :=
  ∑ w ∈ pairEvent s t a b, bucketSize vertices w a
def heavyPairEvent (s t : α → Bool) (a b : K)
    (vertices : Finset (α → Bool)) (B : ℕ) : Finset (α × Bool → K) :=
  (pairEvent s t a b).filter (fun w => B < bucketSize vertices w a)
def trimmedPairEvent (s t : α → Bool) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool)) (B : ℕ) :
    Finset (α × Bool → K) :=
  (pairEvent s t a b).filter (fun w =>
    bucketSize leftVertices w a ≤ B ∧ bucketSize rightVertices w b ≤ B)
end SeparableTrimming
section TrimmedGraphMoments
variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
end TrimmedGraphMoments
end ThreeSum.HashFamily


