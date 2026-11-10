-- Prove2me | Definitions.Def_IntegerMatrixMortality_FixedImage_ModuleGraphs
-- name    : IntegerMatrixMortality_FixedImage_ModuleGraphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:30:49.71934+00:00
-- url     : https://prove2.me/theorems/edaaa5ef-1b54-474f-b98f-538be39ceb9c
-- title:
--   Instruction graphs, valid prefixes, privacy and module requirements
-- statement:
--   A listed edge q→r specifies the single available matrix
--
--   $$C_rM_{\delta,k(p)}D_eM_{1,h(p)}C_q^{-1},\qquad e\in\Delta.$$
--
--   The factors are combined into one generator. An instruction module has entry and exit boundaries and a finite list of these edges. A valid graph walk keeps its input and every complete edge output in V. Completion has positive length and stops at its first arrival at the exit. Allocation to a program identifies boundaries, including coincident entry and exit, and keeps every other occurring phase private to that instruction occurrence.
--
--   The module requirements assert residues in Δ for every valid finite prefix on every unary input; existence and exact output on every allowed input and rejection of every forbidden input; and computable edge formulas, fixed before choosing p. They hold uniformly for every prime p≥7. These are predicates stating what a module must prove, not certificates supplied as axioms to the concrete construction.
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Definition 5.1, PDF p. 8 / printed p. 6; (5.2) and §5.3, PDF pp. 10–11 / printed pp. 8–9

import Mathlib
import Definitions.Def_IntegerMatrixMortality_FixedImage_ProjectiveCodes
import Definitions.Def_IntegerMatrixMortality_FixedImage_ArithmeticProgram

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage


/-- One listed generator formula. The pre-map has sign +1. -/
structure GeneratorEdge where
  source : ℕ
  target : ℕ
  digit : ℤ
  preH : ℕ → ℤ
  postNeg : Bool
  postH : ℕ → ℤ

def localMatrix (p : ℕ) (e : GeneratorEdge) : ZMat :=
  auxiliaryMatrix p e.postNeg (e.postH p) * deletionMatrix p e.digit *
    auxiliaryMatrix p false (e.preH p)

def edgeMatrix (p : ℕ) (e : GeneratorEdge) : ZMat :=
  shiftMatrix e.target * localMatrix p e * inverseShiftMatrix e.source

def localAction (p : ℕ) (e : GeneratorEdge) := projectiveAction (rationalMatrix (localMatrix p e))

structure InstructionModule where
  entry : ℕ
  exit : ℕ
  edges : List GeneratorEdge

/-- A finite graph path with all complete generator values in V, including the input. -/
inductive ValidWalk (p : ℕ) (edges : List GeneratorEdge) :
    ℕ → ProjectivePoint → List GeneratorEdge → ℕ → ProjectivePoint → Prop
  | nil (q : ℕ) (x : ProjectivePoint) (h : Valid p x) : ValidWalk p edges q x [] q x
  | cons (q r : ℕ) (x y : ProjectivePoint) (e : GeneratorEdge) (es : List GeneratorEdge)
      (he : e ∈ edges) (hq : e.source = q) (hx : Valid p x)
      (tail : ValidWalk p edges e.target (localAction p e x) es r y) :
        ValidWalk p edges q x (e :: es) r y

def FirstArrival (w : List GeneratorEdge) (r : ℕ) : Prop :=
  ∀ i : ℕ, i + 1 < w.length → (w[i]?).map GeneratorEdge.target ≠ some r

def Completes (p : ℕ) (M : InstructionModule) (x y : ProjectivePoint) : Prop :=
  ∃ w : List GeneratorEdge, w ≠ [] ∧ FirstArrival w M.exit ∧
    ValidWalk p M.edges M.entry x w M.exit y

def ResiduePrefixes (p : ℕ) (M : InstructionModule) (x : ProjectivePoint)
    (ds : Finset ℤ) : Prop :=
  ∀ w r y, ValidWalk p M.edges M.entry x w r y → InResidues p y ds

def EffectiveModule (M : InstructionModule) : Prop :=
  ∀ e ∈ M.edges, e.digit ∈ delta ∧ Computable e.preH ∧ Computable e.postH

/-- The three requirements of §5.3, on every input and every valid finite prefix. -/
def ModuleRequirements (M : InstructionModule) (f : ℕ → Option ℕ) : Prop :=
  EffectiveModule M ∧ ∀ p : ℕ, Nat.Prime p → 7 ≤ p →
    (∀ n, ResiduePrefixes p M (some (unaryCode p n)) delta) ∧
    (∀ n k, f n = some k → Completes p M (some (unaryCode p n)) (some (unaryCode p k))) ∧
    (∀ n y, Completes p M (some (unaryCode p n)) y →
      ∃ k, f n = some k ∧ y = some (unaryCode p k))

/-- Structural privacy and boundary rules of Definition 5.1 for a collection of modules. -/
def ModuleAllocation (P : ArithmeticProgram) (ms : List InstructionModule) (N : ℕ) : Prop :=
  ms.length = P.edges.length ∧
  (∀ q ∈ P.states, q < N) ∧
  (∀ (i : ℕ) (e : ArithmeticEdge) (M : InstructionModule), P.edges[i]? = some e → ms[i]? = some M →
    M.entry = e.source ∧ M.exit = e.target ∧ M.entry ∈ P.states ∧ M.exit ∈ P.states ∧
    ∀ g ∈ M.edges, g.source < N ∧ g.target < N ∧
      (g.source = M.entry ∨ g.source ∉ P.states) ∧
      (g.target = M.exit ∨ g.target ∉ P.states)) ∧
  (∀ (i j : ℕ) (M K : InstructionModule), ms[i]? = some M → ms[j]? = some K → i ≠ j →
    ∀ g ∈ M.edges, ∀ h ∈ K.edges,
      (g.source ∉ P.states → g.source ≠ h.source ∧ g.source ≠ h.target) ∧
      (g.target ∉ P.states → g.target ≠ h.source ∧ g.target ≠ h.target))

def allocatedGenerators (p : ℕ) (ms : List InstructionModule) : Finset ZMat :=
  (ms.flatMap (fun M => M.edges.map (edgeMatrix p))).toFinset


end IntegerMatrixMortality.FixedImage


