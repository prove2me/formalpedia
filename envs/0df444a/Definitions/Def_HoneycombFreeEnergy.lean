-- Prove2me | Definitions.Def_HoneycombFreeEnergy
-- name    : HoneycombFreeEnergy
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:14.58063+00:00
-- url     : https://prove2.me/theorems/a08274df-6bb5-4a6c-b98b-4acb5e71fb98
-- statement:
--   This block sets up the hexagonal (honeycomb) lattice and the fixed-length forced free energy of its self-avoiding walks. A Vertex has integer column and row coordinates and a boolean flag marking it as an up or down vertex; up(i,j) and down(i,j) build these. The planar position of a vertex in the complex plane has real part col + row/2 + 1/2 (up) or col + row/2 + 1 (down), and imaginary part rowSpacing·(row + 1/3) (up) or rowSpacing·(row + 2/3) (down), where rowSpacing = √3/2. The constant rho is (√(2+√2))⁻¹. Each up vertex (c,r) has the three down neighbors (c,r−1), (c,r) and (c−1,r), and each down vertex (c,r) has the three up neighbors (c,r+1), (c,r) and (c+1,r). walkLists(o,n) is the finite set of all vertex lists of n steps starting at o, and saws(o,n) keeps only those with no repeated vertex, namely the self-avoiding walks. The endpoint is the last vertex (o if the list is empty), displacement is its position minus the position of o, and projection(e,z) is the real part of conj(e)·z, the component of z along the complex direction e. The partition function Z(o,e,s,n) sums, over the self-avoiding walks γ of length n from o, rho^n · exp(s · projection(e, displacement(γ))). logPartition is log Z divided by n, and freeEnergy(o,e,s) is defined as the limit of logPartition as n tends to infinity, taken with Lean's limUnder. This is only a definition of the quantity; the block does not itself assert that the limit exists.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HoneycombFreeEnergy.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HoneycombFreeEnergy.lean; bytes 16..1750
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! Existence of the fixed-length forced free energy of honeycomb walks. -/

noncomputable section
open scoped ENNReal Topology
open Filter

namespace HoneycombForce

structure Vertex where
  col : ℤ
  row : ℤ
  up : Bool
  deriving DecidableEq

def up (i j : ℤ) : Vertex := ⟨i, j, true⟩

def down (i j : ℤ) : Vertex := ⟨i, j, false⟩

def rowSpacing : ℝ := Real.sqrt 3 / 2

def position (v : Vertex) : ℂ :=
  if v.up then
    ⟨(v.col : ℝ) + (v.row : ℝ) / 2 + 1/2,
      rowSpacing * ((v.row : ℝ) + 1/3)⟩
  else
    ⟨(v.col : ℝ) + (v.row : ℝ) / 2 + 1,
      rowSpacing * ((v.row : ℝ) + 2/3)⟩

def rho : ℝ := (Real.sqrt (2 + Real.sqrt 2))⁻¹

def neighbors (v : Vertex) : Finset Vertex :=
  if v.up then
    {down v.col (v.row-1), down v.col v.row, down (v.col-1) v.row}
  else
    {up v.col (v.row+1), up v.col v.row, up (v.col+1) v.row}

def walkLists (o : Vertex) : ℕ → Finset (List Vertex)
  | 0 => {[o]}
  | n+1 => (neighbors o).biUnion (fun v => (walkLists v n).image (List.cons o))

def saws (o : Vertex) (n : ℕ) : Finset (List Vertex) :=
  (walkLists o n).filter List.Nodup

def endpoint (o : Vertex) (γ : List Vertex) : Vertex := γ.getLastD o

def displacement (o : Vertex) (γ : List Vertex) : ℂ :=
  position (endpoint o γ) - position o

def projection (e z : ℂ) : ℝ := (star e * z).re

def partition (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) : ℝ :=
  ∑ γ ∈ saws o n, rho ^ n * Real.exp (s * projection e (displacement o γ))

def logPartition (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) : ℝ :=
  Real.log (partition o e s n) / (n : ℝ)

def freeEnergy (o : Vertex) (e : ℂ) (s : ℝ) : ℝ :=
  Filter.limUnder atTop (logPartition o e s)



end HoneycombForce
end
end OAI


