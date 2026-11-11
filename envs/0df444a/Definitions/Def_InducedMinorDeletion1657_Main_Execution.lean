-- Prove2me | Definitions.Def_InducedMinorDeletion1657_Main_Execution
-- name    : InducedMinorDeletion1657_Main_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:33:02.01172+00:00
-- url     : https://prove2.me/theorems/3c140c3d-9962-421e-85e6-d6996f3d7ee1
-- title:
--   Operational executions, graph encodings and uniform resource bounds
-- statement:
--   Graphs have a fixed adjacency-matrix encoding. RAM inputs are word arrays; input subsets and pair outputs use $n$ membership bits, while subset-family outputs use sorted sparse vertex lists with individual lengths. Collections have a length header followed by their members. The register machine has a finite instruction list, a program counter and random-access memory. A run is the iteration of its published step function to a halted configuration. A word operation costs one step, and output length is also charged. Every memory value throughout the run is at most $(m+T+2)^q$, where $m$ bounds the input length and input words and $T$ is the number of steps; thus words have $O_q(\log(m+T+2))$ bits. There is no oracle instruction or correctness field.
--
--   The goal and bounded-width logical algorithms use actual Mathlib multi-stack Turing machines over four symbols. Their fixed tapes contain the unary vertex count, adjacency bits, and, for budget input only, a delimited unary budget. Output distinguishes failure from every subset, including the empty subset. The run predicate counts actual halting steps.
--
--   The bound functions are
--   $$C2^{C(k+1)^{2/3}\log_2(k+2)}(n+1)^c,\qquad C2^{C(w+1)\log_2(w+2)}(n+1)^c,$$
--   and the explicitly parameterized branching bounds of Sections 3–4. Every theorem chooses constants and programs before all varying inputs. These are predicates of execution and fixed numerical expressions; none assumes algorithmic correctness.
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), Sections 3–6 and Appendix A, pp. 10–28, 37–39 (PDF pp. 11–29, 38–40)

import Definitions.Def_InducedMinorDeletion1657_Main_Logic
import Definitions.Def_MinrankTW_RAM
import Definitions.Def_CFLOutliers_OutputsWithin

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

abbrev Program := List MinrankTW.Instr
abbrev Machine := Turing.TM2ComputableAux OnlineCRS.Combine.Sym OnlineCRS.Combine.Sym

/-- Fixed adjacency-matrix encoding; graph input includes n, never a decomposition or optimum. -/
noncomputable def graphWords (G : InputGraph) : List ℕ :=
  G.n :: ((List.finRange G.n).flatMap fun u =>
    (List.finRange G.n).map fun v => if G.graph.Adj u v then 1 else 0)

noncomputable def subsetWords {n : ℕ} (S : Finset (Fin n)) : List ℕ :=
  (List.finRange n).map fun v => if v ∈ S then 1 else 0

/-- Sparse output: an empty set takes one word even when Δ is much larger than n. -/
noncomputable def sparseWords {n : ℕ} (S : Finset (Fin n)) : List ℕ :=
  S.card :: (S.sort (· ≤ ·)).map Fin.val

noncomputable def familyWords {n : ℕ} (L : List (Finset (Fin n))) : List ℕ :=
  L.length :: L.flatMap sparseWords

noncomputable def pairWords {n : ℕ} (L : List (Finset (Fin n) × Finset (Fin n))) : List ℕ :=
  L.length :: L.flatMap fun p => subsetWords p.1 ++ subsetWords p.2

/-- Input array, length first. The preloaded input is charged only when read. -/
def inputMemory (input : List ℕ) (a : ℕ) : ℕ :=
  if a = 0 then input.length else input[a - 1]?.getD 0

/-- A word-RAM execution of the published elementary register machine. Each instruction costs
    one word operation. All live words have O(log(input size + largest parameter + steps)) bits,
    with uniform multiplier q; no unbounded integer operation is given unit bit cost.
    Output is length at address 0 and its words at successive addresses. Its length is charged.
    This predicate contains execution only, no mathematical correctness assumption. -/
def ramOutputs (P : Program) (input output : List ℕ) (B : ℝ) (q : ℕ) : Prop :=
  ∃ s : ℕ,
    let init : MinrankTW.Config := ⟨0, inputMemory input⟩
    let final := MinrankTW.run P init s
    MinrankTW.IsHalted P final ∧ (s + output.length : ℕ) ≤ B ∧
    final.mem 0 = output.length ∧
    (∀ i : Fin output.length, final.mem (i.val + 1) = output[i]) ∧
    ∀ j ≤ s, ∀ a : ℕ,
      (MinrankTW.run P init j).mem a ≤
        (input.foldl max input.length + s + 2) ^ q

/-- Unary length header and adjacency bits over the published four-symbol alphabet. -/
noncomputable def graphTape (G : InputGraph) : List OnlineCRS.Combine.Sym :=
  List.replicate G.n 1 ++ [2] ++
  ((List.finRange G.n).flatMap fun u => (List.finRange G.n).map fun v =>
    if G.graph.Adj u v then 1 else 0)

noncomputable def answerTape {n : ℕ} (o : Option (Finset (Fin n))) : List OnlineCRS.Combine.Sym :=
  match o with
  | none => [0]
  | some S => 1 :: (List.finRange n).map (fun v => if v ∈ S then 1 else 0)

noncomputable def tableTape {n : ℕ} (L : List (Finset (Fin n))) : List OnlineCRS.Combine.Sym :=
  List.replicate L.length 1 ++ [2] ++ L.flatMap fun S =>
    (List.finRange n).map fun v => if v ∈ S then 1 else 0

noncomputable def budgetTape (G : InputGraph) (b : ℕ) : List OnlineCRS.Combine.Sym :=
  graphTape G ++ [3] ++ List.replicate b 1 ++ [2]

def machineOutputs (P : Machine) (input output : List OnlineCRS.Combine.Sym) (B : ℝ) : Prop :=
  ∃ s : ℕ, (s : ℝ) ≤ B ∧ CFLOutliers.OutputsWithin P input output s

def exactResult (G : InputGraph) (t : ℕ) (φ : Sentence)
    (o : Option (Finset (Fin G.n))) : Prop :=
  match o with
  | none => infeasible G.graph t φ
  | some S => optimal G.graph t φ S

def budgetResult (G : InputGraph) (t : ℕ) (φ : Sentence) (b : ℕ)
    (o : Option (Finset (Fin G.n))) : Prop :=
  match o with
  | none => ¬ ∃ S, feasible G.graph t φ S ∧ S.card ≤ b
  | some S => feasible G.graph t φ S ∧ S.card ≤ b

/-- Parameter of an exact feasible output is its true optimum cardinality; no k for failure. -/
def resultParameter {n : ℕ} (o : Option (Finset (Fin n))) : ℕ :=
  match o with | none => n | some S => S.card

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2
noncomputable def satLog (t : ℕ) : ℝ := logTwo (max 2 (t : ℝ))

/-- All constants in these bounds are quantified before ALL varying inputs in theorems. -/
noncomputable def polyTime (C c : ℕ) (n : ℕ) : ℝ := C * ((n : ℝ) + 1) ^ c
noncomputable def widthTime (C c n w : ℕ) : ℝ :=
  polyTime C c n * (2 : ℝ) ^ (C * ((w : ℝ) + 1) * logTwo ((w : ℝ) + 2))
noncomputable def mainTime (C c n k : ℕ) : ℝ :=
  polyTime C c n * (2 : ℝ) ^
    (C * (((k : ℝ) + 1) ^ ((2 : ℝ) / 3)) * logTwo ((k : ℝ) + 2))
noncomputable def branchCount (C a k d t : ℕ) : ℝ :=
  C * ((k : ℝ) + 2) ^ (C * ((t : ℝ) + 1) ^ a * k / d)
noncomputable def branchTime (C a c n k d t : ℕ) : ℝ :=
  branchCount C a k d t * ((n : ℝ) + 1) ^ c
noncomputable def degenCount (C n Δ t : ℕ) : ℝ :=
  C * ((n : ℝ) + 1) ^ (C * (t : ℝ) ^ 2 * n / Δ)

end InducedMinorDeletion1657.Main


