-- Prove2me | Definitions.Def_StableMSR_ComponentGraphMemory
-- name    : StableMSR_ComponentGraphMemory
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-14T20:07:32.009803+00:00
-- url     : https://prove2.me/theorems/5302c6bf-f250-429e-a824-8937fd13a081
-- title:
--   Edge-array and bitmap input for charged component traversal
-- statement:
--   An ordinary graph input consists of a directed edge list, a zero–one allowed-vertex bitmap, their base addresses, a separate writable reached bitmap, a vertex count, an edge count, and a seed index. Every edge is encoded by two consecutive integer cells. The writable reached cells must be disjoint from both read-only arrays; their initial contents are unrestricted. These definitions specify a composable internal graph primitive for the exact sum-of-radii recovery program. They neither supply the component as advice nor construct the graph from the metric.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, Prove2Me mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b; supporting executable graph primitive for rational_recovery_program.

import Definitions.Def_StableMSR_StructuredCompiler
open scoped Classical
namespace StableMSR.Recovery.ComponentMemory
def address {n : ℕ} (base : ℤ) (v : Fin n) : ℤ := base + (v.val : ℤ)

def Bitmap {n : ℕ} (mem : ℤ → ℤ) (base : ℤ) (S : Finset (Fin n)) : Prop :=
  ∀ v, mem (address base v) = if v ∈ S then 1 else 0

def Separate {n : ℕ} (allowedBase reachedBase : ℤ) : Prop :=
  ∀ u v : Fin n, address allowedBase u ≠ address reachedBase v

def EdgeEncoding {n : ℕ} (mem : ℤ → ℤ) (edgeBase : ℤ)
    (es : List (Fin n × Fin n)) : Prop :=
  ∀ j (hj : j < es.length),
    mem (edgeBase + 2 * (j : ℤ)) = ((es[j]'hj).1.val : ℤ) ∧
    mem (edgeBase + 2 * (j : ℤ) + 1) = ((es[j]'hj).2.val : ℤ)

def EdgesSeparate {n : ℕ} (edgeBase reachedBase : ℤ)
    (es : List (Fin n × Fin n)) : Prop :=
  ∀ j, j < es.length → ∀ v : Fin n,
    edgeBase + 2 * (j : ℤ) ≠ address reachedBase v ∧
    edgeBase + 2 * (j : ℤ) + 1 ≠ address reachedBase v


/-- Ordinary graph input: pointers to edge and allowed arrays, vertex and edge counts,
and a seed index. No initial condition is imposed on the writable reached bitmap. -/
def GraphInput {n : ℕ} (s : Compiler.Store) (A : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) : Prop :=
  s.ptrs 5 = (es.length : ℤ) ∧ s.ptrs 6 = (n : ℤ) ∧
  s.ptrs 17 = (seed.val : ℤ) ∧
  Bitmap s.imem (s.ptrs 3) A ∧ EdgeEncoding s.imem (s.ptrs 2) es ∧
  Separate (n := n) (s.ptrs 3) (s.ptrs 4) ∧
  EdgesSeparate (s.ptrs 2) (s.ptrs 4) es
end StableMSR.Recovery.ComponentMemory


