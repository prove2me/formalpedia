-- Prove2me | Definitions.Def_HypercliqueAC0_FixedDepth_Circuits
-- name    : HypercliqueAC0_FixedDepth_Circuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T19:10:41.731056+00:00
-- url     : https://prove2.me/theorems/a0a7cf3c-9749-40c2-ac71-2b23e9706294
-- title:
--   Gate values, gate depth, output reachability, and ordered prefixes
-- statement:
--   For a De Morgan circuit $C$, a gate value is computed by the same topological evaluation as the circuit output. A gate depth counts the gates on a longest path from an input to that gate, including the gate itself. The output gate is identified by the output source of $C$. A directed path from each gate to the output expresses the pruning convention of §3.2.
--
--   For an abstract AND or OR gate with ordered Boolean input functions $g_1,\ldots,g_t$, its prefixes are
--
--   $$f_j=\bigwedge_{i=1}^j g_i\quad\text{or}\quad f_j=\bigvee_{i=1}^j g_i.$$
--
--   The zeroth prefix is one for AND and zero for OR. For $i\ge1$ define the real increment
--
--   $$d_i=f_i-f_{i-1}.$$
--
--   The same prefix operation is applied to each circuit gate's listed input sources. This gives one common interface for the structural tracing lemma and the probabilistic prefix lemmas.
--
--   **Formalization Note** The general circuit object is imported from `MantriCVQ.ACCircuit`. Gate values and depths use its exact folds. Prefix indices are natural numbers; every theorem uses $1\le j\le t$. The reachability convention is imposed only in Lemma 4.1, where its output exclusion needs it. Numerical circuit bounds use `gates.length`, not the imported wire-inclusive `size`.
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.10 (PDF p.12), §3.2, continuing p.11 (PDF p.13)

import Mathlib
import Definitions.Def_MantriCVQ_ACCircuit
import Definitions.Def_HypercliqueAC0_FixedDepth_Fourier

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Values in the same topological fold as the reused circuit evaluator. -/
def gateValues {X : Type} (C : MantriCVQ.ACCircuit X) (x : X → Bool) : List Bool :=
  C.gates.foldl (fun vals g => vals ++
    [if g.isAnd then g.inputs.all (MantriCVQ.Src.eval x vals)
     else g.inputs.any (MantriCVQ.Src.eval x vals)]) []

def gateValue {X : Type} (C : MantriCVQ.ACCircuit X) (k : Fin C.gates.length) :
    (X → Bool) → Bool := fun x => (gateValues C x).getD k.val false

/-- Depths in the exact fold used by ACCircuit.depth. -/
def gateDepths {X : Type} (C : MantriCVQ.ACCircuit X) : List ℕ :=
  C.gates.foldl (fun ds g => ds ++
    [1 + (g.inputs.map (MantriCVQ.Src.depth ds)).foldr max 0]) []

def gateDepth {X : Type} (C : MantriCVQ.ACCircuit X) (k : Fin C.gates.length) : ℕ :=
  (gateDepths C).getD k.val 0

def isOutputGate {X : Type} (C : MantriCVQ.ACCircuit X) (k : Fin C.gates.length) : Prop :=
  C.output = .gate k.val

/-- Immediate dependency on a gate; paths are oriented from input toward output. -/
def gateFeeds {X : Type} (C : MantriCVQ.ACCircuit X) (a b : Fin C.gates.length) : Prop :=
  MantriCVQ.Src.gate a.val ∈ C.gates[b.val].inputs

/-- The standing pruning convention in §3.2, needed for Lemma 4.1's Moreover clause. -/
def allGatesReachOutput {X : Type} (C : MantriCVQ.ACCircuit X) : Prop :=
  ∃ o : Fin C.gates.length, isOutputGate C o ∧
    ∀ k : Fin C.gates.length, Relation.ReflTransGen (gateFeeds C) k o

/-- The jth prefix of an abstract AND/OR gate. j = 0 gives the correct empty gate. -/
def abstractPrefix {X : Type} (isAnd : Bool) (inputs : List ((X → Bool) → Bool)) (j : ℕ) :
    (X → Bool) → Bool := fun x =>
  if isAnd then (inputs.take j).all (fun f => f x)
  else (inputs.take j).any (fun f => f x)

/-- Inputs in the listed order of the circuit's kth gate. -/
def gateInputs {X : Type} (C : MantriCVQ.ACCircuit X) (k : Fin C.gates.length) :
    List ((X → Bool) → Bool) :=
  C.gates[k.val].inputs.map (fun s x => s.eval x (gateValues C x))

def gatePrefix {X : Type} (C : MantriCVQ.ACCircuit X) (k : Fin C.gates.length) (j : ℕ) :
    (X → Bool) → Bool := abstractPrefix C.gates[k.val].isAnd (gateInputs C k) j

/-- Increment d_i = f_i - f_(i-1), with i ≥ 1 in every use. -/
def prefixIncrement {X : Type} (isAnd : Bool) (inputs : List ((X → Bool) → Bool)) (i : ℕ) :
    (X → Bool) → ℝ := fun x =>
  boolReal (abstractPrefix isAnd inputs i) x - boolReal (abstractPrefix isAnd inputs (i - 1)) x

end HypercliqueAC0.FixedDepth


