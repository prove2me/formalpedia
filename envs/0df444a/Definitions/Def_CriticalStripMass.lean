-- Prove2me | Definitions.Def_CriticalStripMass
-- name    : CriticalStripMass
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:06.343988+00:00
-- url     : https://prove2.me/theorems/fc335039-16ff-4410-8812-0850ee0a825d
-- statement:
--   The strip consists of triangles up(i,j) and down(i,j), indexed by i ∈ ℤ and j ∈ ℕ. Adjacency is symmetric: up(i,j) is adjacent to down(i,j), down(i−1,j), and, when j≥1, down(i,j−1). A path in a strip of height N is a finite list of distinct triangles, starting at up(0,0), ending at a specified triangle, with adjacent successive entries and all vertical indices less than N. Set ρ=1/√(2+√2), c=cos(3π/8), λ=π/8, d=cos(2λ), C=cos λ, and η=2d−1. An arch ending at up(k,0) has weight ρ raised to the number of triangles in its list when k≠0 and the list is such a path, and zero otherwise. A bridge ending at down(k,N−1) has the same weight when N>0 and the list is such a path, and zero otherwise. The arch kernel K(N,k) and bridge kernel sum these respective weights over all finite lists; archMass(N) and bridgeMass(N) then sum their kernels over all integer k. The positive horizontal moment is moment(N)=∑_{k≥1} k K(N,k). StripSumsFinite(N) requires summability of each endpoint-specific path sum, both sums of kernels over integer endpoints, and the moment sum. Two sequences are Comparable if one lies between positive constant multiples of the other for every N≥1, with constants independent of N. CriticalStripMass is the defined proposition that, for every N≥1, all these sums are summable, c·archMass(N)+bridgeMass(N)=1, and bridgeMass(N+1)≤bridgeMass(N); furthermore, moment(N+1)−moment(N) is comparable to bridgeMass(N), moment(N) is comparable to N^(3/4), and bridgeMass(N) is comparable to N^(−1/4).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CriticalStripMass.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CriticalStripMass.lean; bytes 16..2412
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

 

namespace CriticalStrip

noncomputable section
open scoped BigOperators
open Set MeasureTheory

def rho : ℝ := 1 / Real.sqrt (2 + Real.sqrt 2)
def c : ℝ := Real.cos (3 * Real.pi / 8)
def lambda : ℝ := Real.pi / 8
def d : ℝ := Real.cos (2 * lambda)
def C : ℝ := Real.cos lambda
def eta : ℝ := 2 * d - 1

abbrev Triangle := ℤ × ℕ × Bool

def up (i : ℤ) (j : ℕ) : Triangle := (i, j, true)
def down (i : ℤ) (j : ℕ) : Triangle := (i, j, false)

def upDownAdjacent (v w : Triangle) : Prop :=
  v.2.2 = true ∧ w.2.2 = false ∧
    ((v.2.1 = w.2.1 ∧ (w.1 = v.1 ∨ w.1 + 1 = v.1)) ∨
      (v.2.1 = w.2.1 + 1 ∧ v.1 = w.1))

def adjacent (v w : Triangle) : Prop := upDownAdjacent v w ∨ upDownAdjacent w v

 
def IsPath (N : ℕ) (finish : Triangle) (p : List Triangle) : Prop :=
  p.head? = some (up 0 0) ∧ p.getLast? = some finish ∧ p.Nodup ∧
  p.IsChain adjacent ∧ ∀ v ∈ p, v.2.1 < N

 
def archWeight (N : ℕ) (k : ℤ) (p : List Triangle) : ℝ := by
  classical
  exact if k ≠ 0 ∧ IsPath N (up k 0) p then rho ^ p.length else 0

 
def bridgeWeight (N : ℕ) (k : ℤ) (p : List Triangle) : ℝ := by
  classical
  exact if 0 < N ∧ IsPath N (down k (N - 1)) p then rho ^ p.length else 0

def K (N : ℕ) (k : ℤ) : ℝ := ∑' p, archWeight N k p
def bridgeKernel (N : ℕ) (k : ℤ) : ℝ := ∑' p, bridgeWeight N k p
def archMass (N : ℕ) : ℝ := ∑' k : ℤ, K N k
def bridgeMass (N : ℕ) : ℝ := ∑' k : ℤ, bridgeKernel N k
def moment (N : ℕ) : ℝ := ∑' k : ℕ, (k + 1 : ℝ) * K N (k + 1)

 
def StripSumsFinite (N : ℕ) : Prop :=
  (∀ k : ℤ, Summable (archWeight N k)) ∧
  (∀ k : ℤ, Summable (bridgeWeight N k)) ∧
  Summable (K N) ∧ Summable (bridgeKernel N) ∧
  Summable (fun k : ℕ => (k + 1 : ℝ) * K N (k + 1))

 
def Comparable (f g : ℕ → ℝ) : Prop :=
  ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
    ∀ N : ℕ, 1 ≤ N → lo * g N ≤ f N ∧ f N ≤ hi * g N

 
def CriticalStripMass : Prop :=
  (∀ N : ℕ, 1 ≤ N → StripSumsFinite N) ∧
  (∀ N : ℕ, 1 ≤ N → c * archMass N + bridgeMass N = 1) ∧
  Comparable (fun N => moment (N + 1) - moment N) bridgeMass ∧
  Comparable moment (fun N => (N : ℝ) ^ (3 / 4 : ℝ)) ∧
  Comparable bridgeMass (fun N => (N : ℝ) ^ (-(1 / 4) : ℝ)) ∧
  (∀ N : ℕ, 1 ≤ N → bridgeMass (N + 1) ≤ bridgeMass N)

 



end
end CriticalStrip
end OAI


