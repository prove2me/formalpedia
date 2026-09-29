-- Prove2me | Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
-- name    : WilliamsonShmoys_PlanarIndependentSetRAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:17:47.925786+00:00
-- url     : https://prove2.me/theorems/d1783190-afa4-4754-b192-981ba7f5eefc
-- title:
--   Planar drawing and finite unit-cost real RAM
-- statement:
--   Crossing-free planar drawing; finite instruction set, RAM state, deterministic step and run, explicit adjacency and real-weight input layout, and output bitmap.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Theorem 10.11, PDF/manuscript p. 271; weighted problem p. 269 and proof context pp. 270–272. https://doi.org/10.1017/CBO9780511921735.

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
open scoped BigOperators
namespace WilliamsonShmoys

/-- A crossing-free drawing in the plane, manuscript p.270. Each undirected
edge is represented once, with increasing vertex labels. Simple arcs have
no vertex in their interior; different edges meet only at common endpoints.
This is a local concrete adapter, not a published planarity definition. -/
def HasPlanarDrawing {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (p : Fin n → ℝ × ℝ) (arc : Fin n → Fin n → ℝ → ℝ × ℝ),
    Function.Injective p ∧
    (∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧
    (∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
        (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))

/-- A finite instruction set for the unit-cost operation interpretation of
Theorem 10.11. Operands name natural or real cells. Indirect loads/stores use
a natural cell as an address. Only addition, truncated natural subtraction,
real subtraction, and comparisons are available: no optimization oracle,
planarity oracle, arbitrary function instruction, or real-to-integer cast.
Each instruction costs one operation, including a random-access transfer. -/
inductive PlanarRAMInstruction where
  | natConst (dst value : ℕ)
  | natAdd (dst left right : ℕ)
  | natSub (dst left right : ℕ)
  | natLoad (dst addr : ℕ)
  | natStore (addr src : ℕ)
  | realZero (dst : ℕ)
  | realAdd (dst left right : ℕ)
  | realSub (dst left right : ℕ)
  | realLoad (dst addr : ℕ)
  | realStore (addr src : ℕ)
  | natBranch (left right yes no : ℕ)
  | realBranch (left right yes no : ℕ)
  | jump (target : ℕ)
  | halt
  deriving DecidableEq

/-- RAM state. Initial memories have finite support; each step updates at most
one cell. The function representation does not grant bulk access to memory. -/
structure PlanarRAMState where
  pc : ℕ
  natMem : ℕ → ℕ
  realMem : ℕ → ℝ

/-- One deterministic operation. Invalid program counters get stuck; the
capstone requires an actual halt instruction, not an invalid counter. Exact
real comparison is a primitive of this operation model, not a bit algorithm. -/
noncomputable def planarRAMStep (program : List PlanarRAMInstruction)
    (s : PlanarRAMState) : PlanarRAMState := by
  classical
  exact match program[s.pc]? with
  | none => s
  | some .halt => s
  | some (.natConst dst value) =>
      { s with pc := s.pc + 1, natMem := Function.update s.natMem dst value }
  | some (.natAdd dst left right) =>
      { s with pc := s.pc + 1, natMem := Function.update s.natMem dst (s.natMem left + s.natMem right) }
  | some (.natSub dst left right) =>
      { s with pc := s.pc + 1, natMem := Function.update s.natMem dst (s.natMem left - s.natMem right) }
  | some (.natLoad dst addr) =>
      { s with pc := s.pc + 1, natMem := Function.update s.natMem dst (s.natMem (s.natMem addr)) }
  | some (.natStore addr src) =>
      { s with pc := s.pc + 1, natMem := Function.update s.natMem (s.natMem addr) (s.natMem src) }
  | some (.realZero dst) =>
      { s with pc := s.pc + 1, realMem := Function.update s.realMem dst 0 }
  | some (.realAdd dst left right) =>
      { s with pc := s.pc + 1, realMem := Function.update s.realMem dst (s.realMem left + s.realMem right) }
  | some (.realSub dst left right) =>
      { s with pc := s.pc + 1, realMem := Function.update s.realMem dst (s.realMem left - s.realMem right) }
  | some (.realLoad dst addr) =>
      { s with pc := s.pc + 1, realMem := Function.update s.realMem dst (s.realMem (s.natMem addr)) }
  | some (.realStore addr src) =>
      { s with pc := s.pc + 1, realMem := Function.update s.realMem (s.natMem addr) (s.realMem src) }
  | some (.natBranch left right yes no) =>
      { s with pc := if s.natMem left ≤ s.natMem right then yes else no }
  | some (.realBranch left right yes no) =>
      { s with pc := if s.realMem left ≤ s.realMem right then yes else no }
  | some (.jump target) => { s with pc := target }

/-- Exactly t operations, by iteration of the explicit transition function. -/
noncomputable def planarRAMRun (program : List PlanarRAMInstruction)
    (initial : PlanarRAMState) (t : ℕ) : PlanarRAMState :=
  (planarRAMStep program)^[t] initial

/-- Input layout: natural cells 0,1 contain n,k, followed by n² adjacency
entries; real cells 0,...,n-1 contain the weights. All other cells are zero.
The n² table is ordinary input, not an oracle or a supplied embedding.
Accuracy is supplied as the usual integer parameter k, not as a real oracle. -/
def planarRAMInput (n k : ℕ) (edge : Fin n → Fin n → Bool)
    (weight : Fin n → ℝ) : PlanarRAMState where
  pc := 0
  natMem := fun a =>
    if a = 0 then n else if a = 1 then k else
      if hi : (a - 2) / n < n then
        if hj : (a - 2) % n < n then
          if edge ⟨(a - 2) / n, hi⟩ ⟨(a - 2) % n, hj⟩ then 1 else 0
        else 0
      else 0
  realMem := fun a => if h : a < n then weight ⟨a, h⟩ else 0

/-- The n-cell output bitmap immediately after the input adjacency table. -/
def planarRAMOutput (n : ℕ) (s : PlanarRAMState) : Finset (Fin n) :=
  Finset.univ.filter (fun i => s.natMem (2 + n * n + i.val) = 1)

end WilliamsonShmoys


